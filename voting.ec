(* 
  Preliminaries.ec contains:
  - algebraic & cryptographic types
  - ElGamal PKE & abstract PKS
  - operations & axioms that allow messages to be converted into required types
  - operations & axioms about the abstract signature scheme
*)

require import Int.
require import Real.
require import FSet.
require import List.
require import NewFMap.
require import Core.
require import Distr.

require import Preliminaries.
import Preliminaries.
import ElGamal_PKE.
import Abstract_PKS.
pragma Goals:printall.


(* Theory for the simplified voting protocol. 

   Contents:
    1. protocol parties
    2. main game with interaction
    3. stated the security goals with proofs

   Hints about EasyCrypt language:
   1. fst, snd are functions to extract first and second element from a two element tuple.
   2. Let a=(b,c), then a.`1 extracts the first element and a.`2 extracts the second element.
   3. mem - member 
   4. dom - domain
   5. Map elements are accessed with the operation .[]
   6. Map elements are added & updated with the operation .[key <- value]
   7. Option type means that a variable may have either value None or value Some(x) 
   8. oget (Some x) = x
   9. Operation $ is used for sampling from a distribution. FDistr.dt is uniform 
      distribution of field elements. vote = $FDistr.dt; has the meaning that the
      variable vote will get a uniformly chosen value from the distribution FDistr.dt.
*)

theory Voting.
  type ballot = ciphertext * ciphertext.

  op createBallot: ciphertext * ciphertext -> ballot.
  op splitBallot (b:ballot): ciphertext * ciphertext = (b.`1, b.`2).
  
  lemma splitLemma (x,y):
    ((splitBallot(x,y)).`1, (splitBallot(x,y)).`2) = splitBallot(x,y).
    proof. rewrite /splitBallot. trivial. qed.
    
  axiom splitBallot (b:ballot):
    createBallot(splitBallot b) = b.
  
  axiom ballotSplit (x:ciphertext) (y:ciphertext):
    splitBallot(createBallot(x, y)) = (x,y).
  
  op ciphertextToMsg: ciphertext -> message.  
  op ballotToMsg: ballot -> message.
  op keyToMsg: group -> message. 
  op msgToKey: message -> group.
  axiom msgKeyEquality: forall (p:pkey), msgToKey(keyToMsg(p)) = p.


  (** BB specification **)
  module type BBType = {
    proc init(): unit
    proc addVote(vote: plaintext, rr'': group): unit
    proc queryVote(rr'': group): plaintext option
  }.
  
  module BB: BBType = {
    var voteMap: (group, plaintext) fmap 

    proc init() = {
      voteMap = map0;
    }
    
    proc addVote(vote: plaintext , rr'': group) = {
      (* prevent reusing the same receipt *)
      if(mem (dom voteMap) rr'' = false){
        voteMap = voteMap.[rr'' <- vote];
      }
    }
    
    proc queryVote(rr': group) = {
      return voteMap.[rr'];
    }
  }.

  

(*
  The goal of using a blockchain is to assure the integrity of the votes. We 
  assume that blockchain is append only where the entries can not be modified.
*)
  
  module type BCType = {
    proc initBlockChainIndex(): unit 
    proc appendBallot(b: ballot, s: signature): int
    proc getBallot(idx: int): bool * ((ballot * signature) option)
    proc listBallots(): (ballot * signature) list
  }.
  
  module BlockChain: BCType = {
    var bcMap: (int, (ballot * signature)) fmap
    var index: int

    proc initBlockChainIndex() = {
      bcMap = map0;
      index = 0;
    }

    proc appendBallot(b: ballot, s: signature) = {
      bcMap = bcMap.[index <- (b, s)];
      index = index + 1;
      return index - 1;
    }

    proc getBallot(idx: int) = {
      var isValidIdx: bool;
      var content: (ballot * signature) option;

      if(index < idx){
        isValidIdx = false;
        content = witness;
      }
      else{
        isValidIdx = true;
        content = bcMap.[idx];
      }
      
      return (isValidIdx, content);
    }

    proc listBallots() = {
      var ballotList: (ballot * signature) list;
      ballotList = map snd (elems bcMap);
      return ballotList;
    }
  }.



  (** Tallying server specification **)
  module type TallyServerType = {
    proc init(): unit
    proc receiveSecretKey(sk:skey): unit
    proc receiveCAKey(caPk:pkey): unit
    proc receiveKeyDB(m:(pkey, signature) fmap): unit
    proc getTallyPk(): pkey
    proc addBallot(b: ballot): unit
    proc splitDecryptAndPublishBallot(): unit    
  }.

  module TallyServer(BB: BBType): TallyServerType = {
    var pk: pkey
    var sk: skey
    var pk_ca: pkey
    var keyMap: (pkey, signature) fmap
    var ballotList: ballot list 
    
    proc init() = {
      ballotList = [];
    }
    
    proc receiveSecretKey(sk':skey) = {
      sk = sk';
      pk = g ^ sk';
    }

    proc receiveCAKey(caPk:pkey) = {
      pk_ca = caPk;
    }

    proc receiveKeyDB(m:(pkey, signature) fmap) = {
      keyMap = m;
    }

    proc getTallyPk() = {
      return pk;
    }

    proc splitDecryptAndPublishBallot() = {
      var c_1, c_2: ciphertext;
      var vote: plaintext option;
      var rr'': plaintext option;
      var voterBallot: ballot;      
   
      (* simplification to consider a single voter *)
      if(ballotList <> []){
        voterBallot = head witness ballotList;
        ballotList = behead ballotList;

        (c_1, c_2) = splitBallot(voterBallot);
        vote = ElGamal.dec(sk, c_1);
        rr'' = ElGamal.dec(sk, c_2);

        if(vote <> None && rr'' <> None){        
          BB.addVote(oget(vote), oget(rr''));
        }
      }

      (* consider a second voter *)
      if(ballotList <> []){
        voterBallot = head witness ballotList;

        (c_1, c_2) = splitBallot(voterBallot);
        vote = ElGamal.dec(sk, c_1);
        rr'' = ElGamal.dec(sk, c_2);

        if(vote <> None && rr'' <> None){        
          BB.addVote(oget(vote), oget(rr''));
        }
      }
    }
    
    proc addBallot(b: ballot) = {
      ballotList = ballotList ++ [b];
    }   
  }.


  module type KeyHolderType = {
    proc initKeyPair(): unit
    proc getPublicKey(): pkey
    proc setSecretKey(): unit
  }.

  module KeyHolder(T: TallyServerType) = {
    var pk: pkey
    var sk: skey

    proc initKeyPair() = {
      (pk, sk) = ElGamal.kg();
    }
    
    proc getPublicKey() = {
      return pk;
    }

    proc setSecretKey() = {
      T.receiveSecretKey(sk);
    }
  }.


  

  (** Specify voter - it has to be separate from Client such that we 
      could  model malicious client application **)
  module type VoterType = {
    proc chooseCandidate(): unit
    proc getVote(): group
    proc setCombinedRandomness(r: group): unit
    proc verifyBBVote(): bool    
  }.
  
  module Voter(BB: BBType): VoterType = {
    var vote: group
    var bbVote: group option
    var rr_1': group     (* combined random value - used for vote verification *)
    var isVerificationOK: bool
    
    proc chooseCandidate() = {
      var randomVote: F.t;
      randomVote = $FDistr.dt; 
      vote = g^randomVote;
    }

    proc getVote() = {
      return vote;
    }

    proc setCombinedRandomness(r: group): unit = {
      rr_1' = r;
    }    
    
    proc verifyBBVote() = {
      bbVote = BB.queryVote(rr_1');
      if(bbVote <> None && oget(bbVote) = vote){
        isVerificationOK = true;
      }
      else{
        isVerificationOK = false;
      }
      return isVerificationOK;
    }    
  }.

  
  
  (** Client specification **)
  module type ClientType = {
    proc getPk(): pkey
    proc setVote(v: group): unit
    proc genRandomness(): group * ciphertext
    proc verifyServerRandomness(s: signature, r_2: t, pk_r: pkey): bool
    proc createSignedBallot(): (ciphertext * ciphertext) * signature 
    proc getCombinedRandomness(): group
    proc receiveKeyOverSecureChannel(sk_client:skey): unit
    proc setBlockChainIndex(idx: int): unit
    proc isVoteOnBlockChain(): bool
    proc init(): unit
  }.

  module Client (KH: KeyHolderType, BC: BCType): ClientType = {
    var pk: pkey
    var sk: skey
    var pk_tally: pkey
    var r_1: F.t   (* t is defined in PrimeField as field element type *)
    var omega: F.t
    var vote: group
    var c': ciphertext   (* Enc(omega, g^r_1) - encrypted randomness *)
    var rr_1': group     (* combined random value *)   
    var s: signature
    var b: ballot
    var blockChainIndex: int
 

    (* Assume that sk is sent over encrypted & authenticated channel *)
    proc receiveKeyOverSecureChannel(sk_client:skey) = {
      sk = sk_client;
      pk = g ^ sk_client;
      pk_tally = KH.getPublicKey();
    }

    proc init() = {
    }
    
    proc getPk() = {
      return pk;
    }

    proc setVote(v:group) = {
      vote = v;
    }
    
    proc getCombinedRandomness() = {
      return rr_1';
    }
    
    proc genRandomness() = {
      var rr_1: group;
      var c_1: ciphertext;
      r_1 = $FDistr.dt;
      omega = $FDistr.dt;
      rr_1 = g ^ r_1;
      c_1 = ElGamal.enc(pk_tally, omega, rr_1);
      return (rr_1, c_1);
    }

    proc verifyServerRandomness(s: signature, r_2: t, pk_r: pkey): bool = {
      var r: t;
      var isValidSignature: bool;
      r = r_1 + r_2;
      rr_1' = g ^ r;
      c' = ElGamal.enc(pk_tally, omega, rr_1');
      isValidSignature = APKS.verify(pk_r, ciphertextToMsg c', s);
      return isValidSignature;
    }

    proc createSignedBallot() = {
      var encryptedVote : ciphertext;
      var randomElement: t;
      randomElement = $FDistr.dt;
      encryptedVote = ElGamal.enc(pk_tally, randomElement, vote);
      b = (encryptedVote , c');
      s = APKS.sign(sk, ballotToMsg b);
      return (b, s);
    }
    
    proc setBlockChainIndex(idx: int) = {
      blockChainIndex = idx;
    }

    proc isVoteOnBlockChain() = {
      var bc_s: signature;
      var bc_b: ballot;
      var bcresult: (ballot * signature) option;
      var isVoteOnBlockChain: bool;
      var isValidIndex: bool;

      (isValidIndex, bcresult) = BC.getBallot(blockChainIndex);
      (bc_b, bc_s) = oget(bcresult);
      if(isValidIndex = true && bc_s = s && bc_b = b){
        isVoteOnBlockChain = true;
      }
      else{
        isVoteOnBlockChain = false;
      }

      return isVoteOnBlockChain;
    }
  }.
 
  

  (** Server specification **)
  module type ServerType = {
    proc initReceiptKeyPair(): unit
    proc genSignedRandomness(c_1: ciphertext): t * signature * pkey
    proc setSignedBallot(b: ballot, s: signature, pk_client: pkey): unit
    proc receiveCAKey(caPk:pkey): unit
    proc receiveKeyDB(m:(pkey, signature) fmap): unit
  }.

  module Server(T: TallyServerType, BC: BCType, C: ClientType): ServerType = {
    var pk_r: pkey
    var sk_r: skey
    var pk_ca: pkey
    var keyMap: (pkey, signature) fmap
    var hasVotedMap: (pkey, bool) fmap

    proc initReceiptKeyPair() = {
      (pk_r, sk_r) =  ElGamal_PKE.ElGamal.kg();
      hasVotedMap = map0;
    }

    proc receiveCAKey(caPk:pkey) = {
      pk_ca = caPk;
    }
    
    proc receiveKeyDB(m:(pkey, signature) fmap) = {
      keyMap = m;
    }
    
    proc genSignedRandomness(c_1: ciphertext) = {
      var r_2: t;
      var rr_2: group;
      var c_2: ciphertext;
      var c: ciphertext;
      var serverSignature: signature;

      r_2 = $FDistr.dt;
      rr_2 = g ^ r_2;
      c_2 =  ElGamal_PKE.ElGamal.enc(pk_r, F.zero, rr_2);
      c = ElGamal_PKE.mult_ciphertext c_1 c_2;
      serverSignature = Abstract_PKS.APKS.sign(sk_r, ciphertextToMsg c); 
      return (r_2, serverSignature, pk_r);
    }

    proc setSignedBallot(b: ballot, s: signature, pk_client: pkey) = {
      var clientKeySignature: signature;
      var isValidSignature, isValidCASignature: bool;
      var isValidBallot: bool;
      var isNewVoter: bool;
      var blockChainIndex: int;

      (* In case verification succeeds then the ballot is sent to tally server *)
      clientKeySignature = oget(keyMap.[pk_client]);
      isValidCASignature = APKS.verify(pk_ca, keyToMsg pk_client, clientKeySignature);
      isValidSignature = APKS.verify(pk_client, ballotToMsg b, s);
      isValidBallot = APKS.verify(pk_client, ballotToMsg b, s);
      isNewVoter = true;
      if(mem (dom hasVotedMap) pk_client = true){ 
        isNewVoter = ! oget(hasVotedMap.[pk_client]);
      }

      if(isValidCASignature = true
          && isValidSignature = true
          && isNewVoter = true
          && isValidBallot = true){
        T.addBallot(b);
        hasVotedMap = hasVotedMap.[pk_client <- true];
        blockChainIndex = BC.appendBallot(b, s);
        C.setBlockChainIndex(blockChainIndex);      
      }
    }
  }.



  (** CA specification **)
  module type CAType = {
    proc init(): unit
    proc generateClientKey(): unit
    proc finish(): unit
  }.
  
  module CA(S:ServerType, T:TallyServerType, C:ClientType): CAType = {
    var pk_ca: pkey
    var sk_ca: skey
    var keyMap: (pkey, signature) fmap 

    proc init() = {
      (pk_ca, sk_ca) = ElGamal.kg();
      S.receiveCAKey(pk_ca);
      T.receiveCAKey(pk_ca);
      keyMap = map0;
    }

    proc generateClientKey() = {
      var s: signature;
      var pk_client: pkey;
      var sk_client: skey;
      (pk_client, sk_client) = ElGamal.kg();
      C.receiveKeyOverSecureChannel(sk_client);
      s = APKS.sign(sk_ca, keyToMsg pk_client);
      keyMap = keyMap.[pk_client <- s];
    }

    proc finish() = {
      S.receiveKeyDB(keyMap);
      T.receiveKeyDB(keyMap);
    }
  }.  



    
  (** Interaction specification **)
  module Interaction(V: VoterType, C: ClientType, S: ServerType, 
    T: TallyServerType, KH: KeyHolderType, CA: CAType, BC: BCType) = {

    (* initialize blockchain, bulleting board and tally server *)
    proc init():unit = {
      BC.initBlockChainIndex();
      T.init();
      BB.init();

      (* Server generates a keypair for signing receipts *)      
      S.initReceiptKeyPair();

      (* Keyholder initializes tally's keypair, clients can access its public key*)
      KH.initKeyPair();

      (* Init CA - distributes its public key and *)
      CA.init();
    }


    proc main(isInitialized:bool) : bool = {
      var rr_1: group; (* client side of randomnes *)
      var cr: group; (* combined randomness *)
      var c_1: ciphertext;
      var serverSignature: signature;
      var r_2: t;
      var isSignatureValid, isVoteVerified, isValid: bool;
      var b: ballot;
      var signedBallot: signature;
      var pk_server: pkey;
      var cPkey: pkey; 
      var vote: group;
      var isVoteOnBlockChain: bool;

      if(isInitialized = false){
        init();
      }

      (* CA delivers client's secret key over an encrypted & authenticated channel *)
      CA.generateClientKey();
      CA.finish();

      (* Voter chooses the candidate *)
      V.chooseCandidate();
      vote = V.getVote();
      
      (* client - creates & encrypts its part of the randomness *)
      C.setVote(vote);
      (rr_1, c_1) = C.genRandomness();
      
      
      (* server - creates & encrypts its part of the randomness, then it multiplies its own 
         encrypted random value and voter's encrypted random value and signs the result.
         Server returns its part of randomness, plus the signed shared randomness. Voting 
         client verifies the server signature. If verification does not fail, then voting 
         client creates a ballot, signs it and sends the signed vote to the server.
      *)
      (r_2, serverSignature, pk_server) = S.genSignedRandomness(c_1);
      isSignatureValid = C.verifyServerRandomness(serverSignature, r_2, pk_server);
      if(isSignatureValid = true){
        (b, signedBallot) = C.createSignedBallot();
        cPkey = C.getPk();        
        S.setSignedBallot(b, signedBallot, cPkey);
      }

      (* Voter makes sure that voting server added the corresponding vote to blockchain *)
      isVoteOnBlockChain = C.isVoteOnBlockChain();
      if(isVoteOnBlockChain = true){

          (* Now it is time to give tally server access to its secret key *)
          KH.setSecretKey();

          (* Tally server checks if client key was signed by the CA. Next, it verifies the
             voter's signed ballot that is stored on the tally server in encrypted form. In 
             case all checks succeed then tally server uses its secret key to decrypt the 
             ballots. Decryped votes and the corresponding combined random values that act as 
             a receipts are added to the bulleting board. *)
          cPkey = C.getPk();
          T.splitDecryptAndPublishBallot();

          (* Now voter can query if the vote is on the BB *)
          cr = C.getCombinedRandomness();
          V.setCombinedRandomness(cr);
          isVoteVerified = V.verifyBBVote();
          isValid = isVoteVerified;
      }
      else{
        isValid = false;
      }

      return isValid;
    }
  }.




(* Useful lemmas and axioms *)
axiom powerOfUnit: forall(x:t), g1 ^ x = g1.
axiom negationMul: forall(y:t, x: t), y * -x = -x * y.
axiom opPriority: forall(x:t, y:t, z:t), x + y*z + -y*z = y*z + -y*z + x.

lemma mu_zero (P:'a -> bool) (d:'a distr):
    P == pred0 =>
    is_lossless d = true =>
    mu d P = 0%r.
  proof.
  move=> heq.
  progress.
  smt.
  qed.

lemma pow_eq: forall (x:t, y:t), x = y <=> g^x = g^y.
  progress. smt. qed.

lemma ext (f:'a->'b) g: (forall x, f x = g x) => f == g.
  progress. qed.
  
lemma ext2 (f:'a->'b) g:  f == g => (forall x, f x = g x) => f = g.
  rewrite -fun_ext. trivial. qed.

lemma mu_one (P:'a -> bool) (d:'a distr): P == predT => weight d = 1%r => mu d P = 1%r.
  move => heq <-.
  smt. qed. 

lemma oneTrivial: forall(x:t), g ^ (x * F.zero) = g1.
  proof. progress. rewrite mulC. rewrite -pow_pow. rewrite -/g1. apply powerOfUnit. qed.
  
lemma trueTrivial: forall(y:bool), y = true <=> y. by smt. qed.

lemma FZ_inverse: forall(x:t, y:t), x * y + -x * y = F.zero.
    progress. rewrite addfN. trivial. qed.

lemma FZ_inverse2: forall(x:t, y:t), x * y + x * -y = F.zero.
    progress. rewrite mulC. rewrite negationMul. rewrite addfN. trivial. qed.

lemma FZ_inverse3: forall(x:t, y:t, z:t), z + x * y + x * -y = z + F.zero.
    progress. rewrite  mulC. rewrite negationMul. rewrite opPriority.
    rewrite FZ_inverse. rewrite addC. by trivial. qed.
    
lemma FZ_inverse4: forall(x:t, y:t, z:t), z + x * y + -x * y = z + F.zero.
    progress. rewrite  mulC. rewrite opPriority.
    rewrite FZ_inverse. rewrite addC. by trivial. qed.

lemma addZeroToExponent: forall (x:t), g ^ (F.zero + x) = g^x.
    progress. rewrite addC. rewrite addf0. by trivial. qed.

lemma fDistrWeight: weight FDistr.dt = 1%r. by smt. qed.
  
lemma distrFact: mu FDistr.dt (fun (_ : t) => true) = 1%r.
    rewrite mu_one => //=.  by apply fDistrWeight. qed.


  

(* ---------------------------- *)  
(* Start with claims and proofs *)
(* ---------------------------- *)  
  
module B = BB.
module V = Voter(B).  
module T = TallyServer(B).
module KH = KeyHolder(T).
module BC = BlockChain. 
module C = Client(KH, BC). 
module S = Server(T, BC, C).
module CA' = CA(S, T, C).


(** We show correctness of the voting protocol specification **)
lemma votingCorrectness &m:
    Pr[Interaction(V, C, S, T, KH, CA', BC).main(false) @ &m: res = true] = 1%r.
    proof.
      byphoare (_: isInitialized = false ==> res = true) => //=.
      proc.
      inline*. 
      rcondt 1 => //=. 

      rcondt 73 => //=.
      do(wp; rnd; auto). simplify. progress.
      rewrite /mult_ciphertext.
      simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_1 * g ^ (sk80 * omega) * g ^ r_200 * g ^ sk70 ^ F.zero =
        g ^ (r_1 + r_200) * g ^ (sk80 * omega).
        rewrite mulC. rewrite pow_pow. rewrite oneTrivial. 
        rewrite mul1. rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite simpleAlgebra. 
      by apply pks_correctness.
      
      rcondf 105 => //=.
      do(wp; rnd; auto). simplify. progress.   
      by smt.

      rcondt 105 => //=.
      do(wp; rnd; auto). progress. simplify.
      rewrite getP_eq. rewrite oget_some.
      by apply pks_correctness.
      by apply pks_correctness.

      rcondf 116 => //=. 
      do(wp; rnd; auto).     

      rcondt 120 => //=. 
      do(wp; rnd; auto). simplify. progress.
      rewrite getP_eq. rewrite oget_some. by simplify.
      rewrite getP_eq. rewrite oget_some. by simplify.

      rcondt 122 => //=. 
      do(wp; rnd; auto).
    
      rcondt 126 => //=. 
      by do(wp; rnd; auto). 

      rcondt 137 => //=. 
      by do(wp; rnd; auto).

      rcondt 139 => //=. 
      do(wp; rnd; auto). simplify. progress.
      rewrite /splitBallot. simplify. rewrite oget_some. by smt.

      rcondf 140 => //=.
      by do(wp; rnd; auto).

      rcondt 145 => //=. 
      do(wp; rnd; auto; simplify). progress.
      rewrite /splitBallot. simplify. rewrite 2! oget_some.
      by smt. clear H8.
      rewrite oget_some. rewrite /splitBallot.
      rewrite oget_some. simplify.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite mulC. rewrite FZ_inverse3. 
      rewrite addf0. rewrite mulC. rewrite FZ_inverse3.
      rewrite addC. rewrite addf0. rewrite getP_eq.
      rewrite oget_some. by trivial.

      do(wp; rnd; auto). progress. simplify. smt.
      by rewrite distrFact.
      qed.


  
      
(* Lets show that if a malicious client application randomly changes the vote,
   then client can detect the possible anomaly by vote verification. First, 
   we have to specify a malicious client application and then show that the 
   malicious client is not caught only when the randomly changed vote matches 
   the voter's initial choice.
*)
  module MaliciousClient(KH: KeyHolderType, BC: BCType): ClientType = {
    var pk: pkey
    var sk: skey
    var pk_tally: pkey
    var r_1: F.t   (* t is defined in PrimeField as field element type *)
    var omega: F.t
    var vote: group
    var c': ciphertext   (* Enc(omega, g^r_1) - encrypted randomness *)
    var rr_1': group     (* combined random value *)      
    var s: signature
    var b: ballot
    var blockChainIndex: int

    (* Assume that sk is sent over encrypted & authenticated channel *)
    proc receiveKeyOverSecureChannel(sk_client:skey) = {
      sk = sk_client;
      pk = g ^ sk_client;
      pk_tally = KH.getPublicKey();
    }

    proc init() = {
    }    

    proc getPk() = {
      return pk;
    }

    proc setVote(v:group) = {
      var randomVote: F.t;
      randomVote = $FDistr.dt;       
      vote = g ^ randomVote;
    }
    
    proc getCombinedRandomness() = {
      return rr_1';
    }
    
    proc genRandomness() = {
      var rr_1: group;
      var c_1: ciphertext;
      r_1 = $FDistr.dt;
      omega = $FDistr.dt;
      rr_1 = g ^ r_1;
      c_1 = ElGamal.enc(pk_tally, omega, rr_1);
      return (rr_1, c_1);
    }

    proc verifyServerRandomness(s: signature, r_2: t, pk_r: pkey): bool = {
      var r: t;
      var isValidSignature: bool;
      r = r_1 + r_2;
      rr_1' = g ^ r;
      c' = ElGamal.enc(pk_tally, omega, rr_1');
      isValidSignature = APKS.verify(pk_r, ciphertextToMsg c', s);
      return isValidSignature;
    }

    proc createSignedBallot() = {
      var encryptedVote : ciphertext;
      var randomElement: t;
      randomElement = $FDistr.dt;
      encryptedVote = ElGamal.enc(pk_tally, randomElement, vote);
      b = (encryptedVote , c');
      s = APKS.sign(sk, ballotToMsg b);
      return (b, s);
    }

    proc setBlockChainIndex(idx: int) = {
      blockChainIndex = idx;
    }

    proc isVoteOnBlockChain() = {
      var bc_s: signature;
      var bc_b: ballot;
      var bcresult: (ballot * signature) option;
      var isVoteOnBlockChain: bool;
      var isValidIndex: bool;

      (isValidIndex, bcresult) = BC.getBallot(blockChainIndex);
      (bc_b, bc_s) = oget(bcresult);
      if(isValidIndex = true && bc_s = s && bc_b = b){
        isVoteOnBlockChain = true;
      }
      else{
        isVoteOnBlockChain = false;
      }

      return isVoteOnBlockChain;
    }
  }.
      


module AdvMC = MaliciousClient(KH, BC).
module S2 = Server(T, BC, AdvMC).
module CA2 = CA(S, T, AdvMC).

lemma badClientSuccess &m:
    Pr[Interaction(V, AdvMC, S2, T, KH, CA2, BC).main(false) @ &m: res = true] = (1%r/q%r)%Real.
    proof.
      byphoare (_: isInitialized = false ==> res = true) => //=.
      proc.
      inline*. 
      rcondt 1 => //=.

      rcondt 74.
      do(wp; rnd; auto). simplify. progress. 
      rewrite /mult_ciphertext.
      rewrite /fst /snd. simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_1 * g ^ (sk80 * omega) * g ^ r_200 * g ^ (sk70 * F.zero) =
        g ^ (r_1 + r_200) * g ^ (sk80 * omega).
        rewrite mulC. rewrite oneTrivial. rewrite mul1. 
        rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite -simpleAlgebra. 
      rewrite oneTrivial. rewrite pow_pow. rewrite oneTrivial.
      by apply pks_correctness.
    
      rcondf 106 => //=.
      do(wp; rnd; auto). simplify. progress.
      by smt.

      rcondt 106. 
      do(wp; rnd; auto). simplify. progress. 
      rewrite getP_eq. rewrite oget_some.
      apply pks_correctness.
      by apply pks_correctness.

      (* Here starts the relevant part of the proof - selects randomvote sampling *)
      seq 36: (vote=g^randomVote0) (1%r/q%r) (1%r) (1%r-1%r/q%r) (0%r)
      (MaliciousClient.pk_tally = KeyHolder.pk
        /\ MaliciousClient.pk = pk_client
        /\ TallyServer.pk_ca = CA.pk_ca
        /\ Server.pk_r = g ^ sk7
        /\ Server.sk_r = sk7
        /\ KeyHolder.sk = sk8
        /\ KeyHolder.pk = g ^ sk8
        /\ TallyServer.ballotList = []
        /\ BlockChain.index = 0
        /\ BB.voteMap = map0 
        /\ vote = Voter.vote
        /\ Voter.vote = g ^ randomVote
        /\ TallyServer.keyMap = CA.keyMap
        /\ s = sign(CA.sk_ca, keyToMsg pk_client)
        /\ CA.keyMap.[pk_client] = Some s).
      do(wp;rnd;wp). skip. progress. 
      rewrite getP_eq. by trivial.

      seq 35: (MaliciousClient.pk_tally = KeyHolder.pk
      /\ MaliciousClient.pk = pk_client
      /\ TallyServer.pk_ca = CA.pk_ca
      /\ Server.pk_r = g ^ sk7
      /\ Server.sk_r = sk7
      /\ KeyHolder.sk = sk8
      /\ KeyHolder.pk = g ^ sk8
      /\ TallyServer.ballotList = []
      /\ BlockChain.index = 0
      /\ BB.voteMap = map0   
      /\ vote = Voter.vote
      /\ Voter.vote = g ^ randomVote  
      /\ TallyServer.keyMap = CA.keyMap
      /\ s = sign(CA.sk_ca, keyToMsg pk_client)
      /\ CA.keyMap.[pk_client] = Some s) (1%r/q%r).
      by trivial.

      cut onePr: 1%r = inv (q%r / q%r). by smt.
      do(wp;rnd;wp). skip. simplify. 
      rewrite mu_one => //=. move => x.
      rewrite mu_one => //=. move => x1.
      rewrite mu_one => //=. move => x2.
      rewrite -onePr.
      rewrite mu_one => //=. move => x3.
      rewrite mu_one => //=. move => x4.
      rewrite getP_eq. simplify. by trivial.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.

      rnd (fun v => vote = g ^ v).
      skip. simplify. progress.

      pose rV := randomVote{hr}.
      cut H1: (fun (v:t) => g ^ rV = g ^ v) = pred1 rV.
      apply ext2. apply ext. progress.
        rewrite /pred1.  simplify. rewrite pow_bij. smt.
      progress. rewrite /pred1. rewrite pow_bij.  smt.
      rewrite H1 => {H1}.      
      cut H2: mu FDistr.dt (pred1 rV) = mu1 FDistr.dt rV. by rewrite /mu1.      
      rewrite H2 => {H2}. 
      by rewrite FDistr.dt1E.

      do(wp;rnd;wp). skip. progress. 
      rewrite mu_one => //=. move => x. 
      rewrite mu_one => //=. move => x1.
      rewrite mu_one => //=. move => x2.
      rewrite mu_one => //=. move => x3.
      rewrite getP_eq. simplify.
      rewrite mu0. simplify. by trivial.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      simplify. by smt.

      rcondf 81. 
      by do(wp; rnd; auto).

      rcondt 85.
      do(wp; rnd; auto). simplify. progress. 
      rewrite getP_eq. rewrite oget_some. by simplify.
      rewrite getP_eq. rewrite oget_some. by simplify.

      rcondt 87. 
      by do(wp; rnd; auto). 

      rcondt 91. 
      by do(wp; rnd; auto). 

      rcondt 102. 
      by do(wp; rnd; auto).       

      rcondt 104. 
      do(wp; rnd; auto). simplify. progress.
      rewrite /splitBallot. simplify. rewrite oget_some. 
      rewrite 2! pow_pow. rewrite 2!  mul_pow. rewrite negationMul.
      rewrite FZ_inverse4. by smt.
      
      rcondf 105. 
      by do(wp; rnd; auto). 

      rcondt 110. 
      do(wp; rnd; auto). simplify. progress.
      rewrite /splitBallot. simplify. rewrite 2! oget_some.
      by smt. clear H5.
      rewrite oget_some. simplify.      
      rewrite /splitBallot. simplify.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite mulC. rewrite FZ_inverse3. 
      rewrite addf0. rewrite mulC. rewrite FZ_inverse3.
      rewrite addC. rewrite addf0. rewrite getP_eq.
      rewrite oget_some. rewrite H0. by trivial. 

      do(wp;rnd;wp). skip. progress.
      rewrite 4! distrFact. by trivial.

      rcondf 81. 
      by do(wp; rnd; auto).

      rcondt 85.
      do(wp; rnd; auto). simplify. progress. 
      rewrite getP_eq. rewrite oget_some. by simplify.
      rewrite getP_eq. rewrite oget_some. by simplify.

      rcondt 87. 
      by do(wp; rnd; auto). 

      rcondt 91. 
      by do(wp; rnd; auto).

      rcondt 102.
      by do(wp; rnd; auto).

      rcondt 104. 
      do(wp; rnd; auto). simplify. progress.
      rewrite /splitBallot. simplify. rewrite oget_some. 
      rewrite 2! pow_pow. rewrite 2!  mul_pow. rewrite negationMul.
      rewrite FZ_inverse4. by smt.
      
      rcondf 105. 
      by do(wp; rnd; auto). 
 
      rcondf 110.
      do(wp; rnd; auto). simplify. progress.
      rewrite /splitBallot. simplify. rewrite 2! oget_some.
      rewrite /splitBallot. simplify.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite mulC. rewrite FZ_inverse3. 
      rewrite addf0. rewrite mulC. rewrite FZ_inverse3.
      rewrite addC. rewrite addf0. rewrite getP_eq.
      rewrite oget_some. progress. 
      rewrite eq_sym. rewrite H0. by trivial. 
     
      do(wp;rnd;wp). skip. progress.
      rewrite mu_one => //=. move => a.
      rewrite mu_one => //=. move => b.    
      rewrite mu_one => //=. move => c.    
      rewrite /predT. rewrite trueTrivial.
      rewrite mu0 => //=.
      rewrite fDistrWeight => //=.
      rewrite fDistrWeight => //=.
      by rewrite fDistrWeight => //=.
      by trivial.
      qed.



      
  module MaliciousServer(T: TallyServerType, BC: BCType, C: ClientType): ServerType = {
    var pk_r: pkey
    var sk_r: skey
    var pk_ca: pkey
    var keyMap: (pkey, signature) fmap

    proc initReceiptKeyPair() = {
      (pk_r, sk_r) =  ElGamal_PKE.ElGamal.kg();
    }

    proc receiveCAKey(caPk:pkey) = {
      pk_ca = caPk;
    }
    
    proc receiveKeyDB(m:(pkey, signature) fmap) = {
      keyMap = m;
    }
    
    proc genSignedRandomness(c_1: ciphertext) = {
      var r_2: t;
      var rr_2: group;
      var c_2: ciphertext;
      var c: ciphertext;
      var serverSignature: signature;

      r_2 = $FDistr.dt;
      rr_2 = g ^ r_2;
      c_2 =  ElGamal_PKE.ElGamal.enc(pk_r, F.zero, rr_2);
      c = ElGamal_PKE.mult_ciphertext c_1 c_2;
      serverSignature = Abstract_PKS.APKS.sign(sk_r, ciphertextToMsg c); 
      return (r_2, serverSignature, pk_r);
    }

    proc setSignedBallot(b: ballot, s: signature, pk_client: pkey) = {
      var clientKeySignature: signature;
      var isValidSignature: bool;
      var blockChainIndex: int;

      clientKeySignature = oget(keyMap.[pk_client]);
      isValidSignature = APKS.verify(pk_ca, keyToMsg pk_client, clientKeySignature);
      (* if(isValidSignature = true){
           T.addBallot(b);
         }
      *)
     
      blockChainIndex = BC.appendBallot(b, s);
      C.setBlockChainIndex(blockChainIndex);
    }
  }.

module B3= BB.
module V3 = Voter(B3).  
module T3 = TallyServer(B3).
module KH3 = KeyHolder(T3).
module BC3 = BlockChain. 
module C3 = Client(KH3, BC3).       
module Adv_S = MaliciousServer(T3, BC3, C3).
module CA3 = CA(Adv_S, T3, C3).

lemma voteDeletingVServer &m:
    Pr[Interaction(V3, C3, Adv_S, T3, KH3, CA3, BC3).main(false) @ &m: res = true] = 0%r.
    proof.
      byphoare (_: isInitialized = false ==> res = true) => //=.    
      proc.
      inline*.
      rcondt 1 => //=.

      (* we need to state this local lemma about the FDistr to avoid problems later *)
      cut distrFact: mu FDistr.dt (fun (_ : t) => true) = 1%r. by smt.
    
      rcondt 72 => //=.
      do(wp; rnd; auto). simplify. progress. 
      rewrite /mult_ciphertext.
      simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_1 * g ^ (sk80 * omega) * g ^ r_200 * g ^ sk70 ^ F.zero =
        g ^ (r_1 + r_200) * g ^ (sk80 * omega).
        rewrite mulC. rewrite pow_pow. rewrite oneTrivial. 
        rewrite mul1. rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite simpleAlgebra. 
      by apply pks_correctness.
    
      rcondf 101 => //=.
      by do(wp; rnd; auto).

      rcondt 105 => //=.
      do(wp; rnd; auto). simplify. progress.
      rewrite getP_eq. rewrite oget_some. by simplify.
      simplify. rewrite getP_eq. rewrite oget_some. by simplify.

      rcondt 107 => //=.
      by do(wp; rnd; auto).

      rcondf 111 => //=.
      do(wp; rnd; auto). 
    
      rcondf 111 => //=.
      do(wp; rnd; auto). 

      rcondf 116 => //=.
      do(wp; rnd; auto). simplify. progress. by smt.
    
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. skip. progress.
      rewrite mu_one => //=. move => x1. 
      rewrite mu_one => //=. move => x2.
      rewrite mu_one => //=. move => x3.
      rewrite mu_one => //=. move => x4.
      rewrite /predT. rewrite trueTrivial. by smt.
      rewrite /predT. rewrite distrFact. by simplify.
      rewrite /predT. rewrite distrFact. by simplify.
      by apply distrFact.
      by apply distrFact.
      qed.  


  module MaliciousTally(BB: BBType): TallyServerType = {
    var pk: pkey
    var sk: skey
    var pk_ca: pkey
    var keyMap: (pkey, signature) fmap
    var ballotList: ballot list 
    
    proc init() = {
      ballotList = [];
    }
    
    proc receiveSecretKey(sk':skey) = {
      sk = sk';
      pk = g ^ sk';
    }

    proc receiveCAKey(caPk:pkey) = {
      pk_ca = caPk;
    }

    proc receiveKeyDB(m:(pkey, signature) fmap) = {
      keyMap = m;
    }

    proc getTallyPk() = {
      return pk;
    }

    proc splitDecryptAndPublishBallot() = {
      var c_1, c_2: ciphertext;
      var vote: plaintext option;
      var rr'': plaintext option;
      var voterBallot: ballot;      

      (* simplification to consider a single voter *)
      if(ballotList <> []){
        voterBallot = head witness ballotList;

        (c_1, c_2) = splitBallot(voterBallot);
        vote = ElGamal.dec(sk, c_1);
        rr'' = ElGamal.dec(sk, c_2);

        (* do not add vote to the BB 
          if(vote <> None && rr'' <> None){        
            BB.addVote(oget(vote), oget(rr''));
          }
        *)
      }
    }
    
    proc addBallot(b: ballot) = {
      ballotList = ballotList ++ [b];
    }   
  }.

module B4 = BB.
module V4 = Voter(B4).  
module Adv_TS = MaliciousTally(B4).
module KH4 = KeyHolder(Adv_TS).
module BC4 = BlockChain. 
module C4 = Client(KH4, BC4).       
module S4 = MaliciousServer(Adv_TS, BC4, C4).
module CA4 = CA(S4, Adv_TS, C4).

lemma voteDeletingTally &m:
    Pr[Interaction(V4, C4, S4, Adv_TS, KH4, CA4, BC4).main(false) @ &m: res = true] = 0%r.
    proof.
      byphoare (_: isInitialized = false ==> res = true) => //=.
      proc.
      inline*.
      rcondt 1 => //=.

      (* we need to state this local lemma about the FDistr to avoid problems later *)
      cut distrFact: mu FDistr.dt (fun (_ : t) => true) = 1%r. by smt.
    
      rcondt 72 => //=.
      do(wp; rnd; auto). simplify. progress. 
      rewrite /mult_ciphertext.
      simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_1 * g ^ (sk60 * omega) * g ^ r_200 * g ^ sk50 ^ F.zero =
        g ^ (r_1 + r_200) * g ^ (sk60 * omega).
        rewrite mulC. rewrite pow_pow. rewrite oneTrivial. 
        rewrite mul1. rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite simpleAlgebra. 
      by apply pks_correctness.
    
      rcondf 101 => //=.
      by do(wp; rnd; auto).

      rcondt 105 => //=.
      do(wp; rnd; auto). simplify. progress.
      rewrite getP_eq. rewrite oget_some. by simplify.
      simplify. rewrite getP_eq. rewrite oget_some. by simplify.

      rcondt 107 => //=.
      by do(wp; rnd; auto).

      rcondf 111 => //=.
      do(wp; rnd; auto). 
    
      rcondf 116 => //=.
      do(wp; rnd; auto). simplify. progress. by smt.
    
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. rnd. simplify.
      wp. rnd. wp. skip. progress.
      rewrite mu_one => //=. move => x1. 
      rewrite mu_one => //=. move => x2.
      rewrite mu_one => //=. move => x3.
      rewrite mu_one => //=. move => x4.
      rewrite /predT. rewrite trueTrivial. by smt.
      rewrite /predT. rewrite distrFact. by simplify.
      rewrite /predT. rewrite distrFact. by simplify.
      by apply distrFact.
      by apply distrFact.
      qed.  




(* Specify the receipt foring voting client who could be deployed using a botnet *)
  module ReceiptForgingClient (KH: KeyHolderType, BC: BCType) = {
    var pk: pkey
    var sk: skey
    var pk_tally: pkey
    var r_1: F.t   (* t is defined in PrimeField as field element type *)
    var omega: F.t
    var vote: group
    var forgedVote: group
    var c': ciphertext   (* Enc(omega, g^r_1) - encrypted randomness *)
    var rr_1': group     (* combined random value *)   
    var s: signature
    var b: ballot
    var blockChainIndex: int
    var receiptMap: (group, ballot * group) fmap

    (* Assume that sk is sent over encrypted & authenticated channel *)
    proc receiveKeyOverSecureChannel(sk_client:skey) = {
      sk = sk_client;
      pk = g ^ sk_client;
      pk_tally = KH.getPublicKey();
    }
    
    proc init() = {
      receiptMap = map0;
    }
    
    proc getPk() = {
      return pk;
    }

    proc setVote(v:group) = {
      vote = v;
    }
    
    proc getCombinedRandomness() = {
      return rr_1';
    }
    
    proc genRandomness() = {
      var rr_1: group;
      var c_1: ciphertext;
      r_1 = $FDistr.dt;
      omega = $FDistr.dt;
      rr_1 = g ^ r_1;
      c_1 = ElGamal.enc(pk_tally, omega, rr_1);
      return (rr_1, c_1);
    }

    proc verifyServerRandomness(s: signature, r_2: t, pk_r: pkey): bool = {
      var r: t;
      var isValidSignature: bool;
      r = r_1 + r_2;
      rr_1' = g ^ r;
      c' = ElGamal.enc(pk_tally, omega, rr_1');
      isValidSignature = APKS.verify(pk_r, ciphertextToMsg c', s);
      return isValidSignature;
    }

    proc createSignedBallot() = {
      var encryptedVote : ciphertext;
      var randomElement: t;
      randomElement = $FDistr.dt;

      (* a) if vote is not in the receipt map --> behave honestly 
         b) receipt for vote exists in receipt map --> forge 
            vote if shared randomness is unique 
      *)
      if(mem (dom receiptMap) vote = false){ 
        encryptedVote = ElGamal.enc(pk_tally, randomElement, vote);
        b = (encryptedVote, c');
        s = APKS.sign(sk, ballotToMsg b);
        receiptMap = receiptMap.[vote <- (b, rr_1')];
      }
      else{
        forgedVote = g ^ F.one;
        if(rr_1' <> snd (oget(receiptMap.[vote]))){
          encryptedVote = ElGamal.enc(pk_tally, randomElement, forgedVote);
          c' = ElGamal.enc(pk_tally, omega, rr_1');
        }
        else{
          encryptedVote = ElGamal.enc(pk_tally, randomElement, vote);
        }
        
        b = (encryptedVote, c');
        s = APKS.sign(sk, ballotToMsg b);
        rr_1' = (snd (oget(receiptMap.[vote])));
      }
      return (b, s);
    }
    
    proc setBlockChainIndex(idx: int) = {
      blockChainIndex = idx;
    }

    proc isVoteOnBlockChain() = {
      var bc_s: signature;
      var bc_b: ballot;
      var bcresult: (ballot * signature) option;
      var isVoteOnBlockChain: bool;
      var isValidIndex: bool;

      (isValidIndex, bcresult) = BC.getBallot(blockChainIndex);
      (bc_b, bc_s) = oget(bcresult);
      if(isValidIndex = true && bc_s = s && bc_b = b){
        isVoteOnBlockChain = true;
      }
      else{
        isVoteOnBlockChain = false;
      }

      (* We have two parties,  so we can use 2 to reset the value such that the check on the 
         bulletin board would fail in case the voter did not get a fresh blockchainindex. *)
      blockChainIndex = 2;
      return isVoteOnBlockChain;
    }
  }.
 

  module VoterFor0(BB: BBType): VoterType = {
    var vote: group
    var bbVote: group option
    var rr_1': group     (* combined random value - used for vote verification *)
    var isVerificationOK: bool
    
    proc chooseCandidate() = {
      vote = g^F.zero;
    }

    proc getVote() = {
      return vote;
    }

    proc setCombinedRandomness(r: group): unit = {
      rr_1' = r;
    }    
    
    proc verifyBBVote() = {
      bbVote = BB.queryVote(rr_1');
      if(bbVote <> None && oget(bbVote) = vote){
        isVerificationOK = true;
      }
      else{
        isVerificationOK = false;
      }
      return isVerificationOK;
    }    
  }.


  (** Voting process of two voters with the receipt forging voting client **)
  module ReceiptForgery(V0: VoterType, V1: VoterType, Adv_C: ClientType, S: ServerType, 
    T: TallyServerType, KH: KeyHolderType, CA: CAType, BC: BCType) = {

    module I1 = Interaction(V0, Adv_C, S, T, KH, CA, BC)
    module I2 = Interaction(V1, Adv_C, S, T, KH, CA, BC)
    
    proc main() : bool = {  
      var isValid1, isValid2: bool;

      Adv_C.init();
      isValid1 = I1.main(false);
      isValid2 = I2.main(true);

      return isValid1 && isValid2;
    }   
  }.


module B5= BB.
module V5 = VoterFor0(B5).  
module T5 = TallyServer(B5).
module KH5 = KeyHolder(T5).
module BC5 = BlockChain. 
module Adv_C = ReceiptForgingClient(KH5, BC5).       
module S5 = Server(T5, BC5, Adv_C).
module CA5 = CA(S5, T5, Adv_C).

(* We simplify the proof by assuming that the receipts are generated fresh and that they do not
   repeat. Adding the restriction would require the votingserver to check that the receipt has 
   not been generated before. Currently this is ignored and the corresponding subgoal about the
   possible repeating receipts admitted.
*)
lemma clashAttack &m:
    Pr[ReceiptForgery(V5, V5, Adv_C, S5, T5, KH5, CA5, BC5).main() @ &m: res = false] =
      (1%r/q%r)%Real.
    proof.
      byphoare => //=.
      proc.
      inline*.

      rcondt 3 => //=.
      wp. skip. progress.
    
      rcondt 74 => //=.
      do(wp; rnd; auto). simplify. progress. 
      rewrite /mult_ciphertext.
      simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_1 * g ^ (sk18 * omega) * g ^ r_21 * g ^ sk17 ^ F.zero =
        g ^ (r_1 + r_21) * g ^ (sk18 * omega).
        rewrite mulC. rewrite pow_pow. rewrite oneTrivial. 
        rewrite mul1. rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite simpleAlgebra. 
      by apply pks_correctness.

      rcondt 75 => //=.
      do(wp; rnd; auto). simplify. progress.
      by smt.

      rcondf 107 => //=.
      do(wp; rnd; auto). simplify. progress.
      by smt.

      rcondt 107 => //=.
      do(wp; rnd; auto). simplify. progress. 
      rewrite getP_eq. rewrite oget_some.
      by apply pks_correctness.
      by apply pks_correctness.

      rcondf 118 => //=. 
      by do(wp; rnd; auto).

      rcondt 122 => //=. 
      do(wp; rnd; auto). simplify. progress.
      rewrite getP_eq. rewrite oget_some. by simplify.
      rewrite getP_eq. rewrite oget_some. by simplify.

      rcondt 125 => //=. 
      by do(wp; rnd; auto).

      rcondt 129 => //=. 
      by do(wp; rnd; auto).

      rcondt 140 => //=. 
      by do(wp; rnd; auto).

      rcondt 142 => //=. 
      do(wp; rnd; auto). simplify. progress.
      rewrite oget_some. rewrite /splitBallot. simplify. by smt.
    
      rcondf 143 => //=. 
      by do(wp; rnd; auto).

      rcondt 148 => //=. 
      do(wp; rnd; auto; simplify). progress.
      rewrite /splitBallot. simplify. rewrite 2! oget_some.
      by smt. clear H7.
      rewrite oget_some. rewrite /splitBallot.
      rewrite oget_some. simplify.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite mulC. rewrite FZ_inverse3. 
      rewrite addf0. rewrite mulC. rewrite FZ_inverse3.
      rewrite addC. rewrite addf0. rewrite getP_eq.
      rewrite oget_some. by trivial.

      rcondf 153 => //=.
      by do(wp; rnd; auto).

    
      (* Here starts the proof about matching keys, i.e., 1%r/q%r of the result probability *)
      swap 19 -18.
      swap 153 -151.
      seq 2: (sk=sk8) (1%r/q%r) (1%r) (1%r - 1%r/q%r) (0%r)  => //=.

      seq 1: (sk \in FDistr.dt) (inv q%r).
      rnd. simplify. progress.
      cut onePr: 1%r =  (inv q%r) / (inv q%r). smt.  
      do(wp;rnd;wp). skip. simplify. 
      rewrite -onePr. by smt.


      rnd (fun sk8 => sk = sk8). skip. simplify. progress.
      pose rSk := sk{hr}. 
      cut H1: (fun (s:t) => rSk = s) = (pred1 rSk).
      apply ext2. apply ext. progress.
        rewrite /pred1. smt.
      progress. rewrite /pred1.  smt.
      rewrite H1 => {H1}.      
      cut H2: mu FDistr.dt (pred1 rSk) = mu1 FDistr.dt rSk. by trivial.
      by rewrite FDistr.dt1E. 
    
      do(wp;rnd;wp). skip. progress. 
      rewrite mu_zero => //=. move => x. rewrite /pred0. smt.
      rewrite /is_lossless. rewrite fDistrWeight => //=.
      move => _ _. by smt.


      rcondt 206.
      do(wp; rnd; auto). simplify. progress. 
      rewrite /mult_ciphertext.
      simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_10 * g ^ (sk180 * omega0) * g ^ r_230 * g ^ sk170 ^ F.zero =
        g ^ (r_10 + r_230) * g ^ (sk180 * omega0).
        rewrite mulC. rewrite pow_pow. rewrite oneTrivial. 
        rewrite mul1. rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite simpleAlgebra. 
      by apply pks_correctness.

      rcondf 207 => //=.
      do(wp; rnd; auto). simplify. progress.
      by smt.
    
      (* isNewVoter = false *)
      rcondt 237 => //=.
      do(wp; rnd; auto). simplify. progress.
      by smt.

      rcondf 238 => //=.
      do(wp; rnd; auto). simplify. progress. clear H10.
      rewrite getP_eq. rewrite oget_some.
      rewrite getP_eq. rewrite oget_some.
      rewrite getP_eq. rewrite oget_some.
      rewrite getP_eq. by trivial.

      rcondt 239 => //=. 
      by do(wp; rnd; auto).

      rcondf 243 => //=. 
      by do(wp; rnd; auto).
    
      rcondf 246 => //=. 
      by do(wp; rnd; auto).

      do(wp; rnd; auto). simplify. progress.
      rewrite fDistrWeight. by trivial.
      by smt.


      rcondt 206.
      do(wp; rnd; auto). simplify. progress. 
      rewrite /mult_ciphertext.
      simplify. rewrite mul_pow. rewrite addf0.
      rewrite pow_pow. rewrite mulA.
      cut simpleAlgebra: g ^ r_10 * g ^ (sk180 * omega0) * g ^ r_230 * g ^ sk170 ^ F.zero =
        g ^ (r_10 + r_230) * g ^ (sk180 * omega0).
        rewrite mulC. rewrite pow_pow. rewrite oneTrivial. 
        rewrite mul1. rewrite mulC. rewrite mulA. rewrite mul_pow. 
        rewrite addC. by trivial.
      rewrite simpleAlgebra. 
      by apply pks_correctness.

      rcondf 207 => //=.
      do(wp; rnd; auto). simplify. progress. by smt.
    
      (* isNewVoter = true *)
      rcondf 237 => //=.
      do(wp; rnd; auto). simplify. progress. by smt.       

      rcondt 237 => //=.
      do(wp; rnd; auto). simplify. progress. clear H10 H11.
      rewrite getP_eq. rewrite oget_some. apply pks_correctness. clear H10 H11 H12.
      by apply pks_correctness. clear H11.
      rewrite getP_eq. rewrite oget_some. by apply pks_correctness. clear H11 H12.
      by apply pks_correctness. 

      rcondf 248 => //=. 
      by do(wp; rnd; auto).

      rcondt 252 => //=. 
      do(wp; rnd; auto). simplify. progress. clear H10 H11.
      do(rewrite getP_eq; rewrite oget_some). progress. 
      do(rewrite getP_eq; rewrite oget_some). progress.
      do(rewrite getP_eq; rewrite oget_some). progress.
      do(rewrite getP_eq; rewrite oget_some). progress.

      rcondt 255 => //=. 
      by do(wp; rnd; auto).

      rcondt 259 => //=. 
      by do(wp; rnd; auto).
   
      rcondt 270 => //=. 
      by do(wp; rnd; auto).

      rcondt 272 => //=. 
      do(wp; rnd; auto). simplify. progress.
      rewrite /splitBallot. simplify. rewrite 3! oget_some. by smt.
      rewrite /splitBallot. simplify. rewrite 3! oget_some. 
      (* here we say that g ^ (r_1 + r_210) <> g ^ (r_10 + r_230) as in the protocol the 
         votingserver could check and make sure that the receipts are not repeated. We omitted 
         this check in EasyCrypt to make the proof simpler.
      *)
      admit.

      rcondf 273 => //=. 
      do(wp; rnd). simplify. progress.
      wp. skip. simplify. by trivial.
      
      rcondt 278 => //=.
      do(wp; rnd). simplify. wp. skip. simplify. progress.
      rewrite /splitBallot. simplify. clear H10 H11.
      rewrite getP_eq. rewrite 5! oget_some. smt.
      clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.


      rewrite /splitBallot. simplify.
      rewrite 4! oget_some. rewrite getP_eq. rewrite oget_some.
      progress. rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite 2! negationMul. 
      rewrite 2! FZ_inverse4. rewrite 2! addf0.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite 2! negationMul. 
      rewrite 2! FZ_inverse4. rewrite 2! addf0. 
      (* here we say that g ^ (r_1 + r_210) <> g ^ (r_10 + r_230) as in the protocol the 
         votingserver could check and make sure that the receipts are not repeated. We omitted 
         this check in EasyCrypt to make the proof simpler.
      *)
      admit.

      clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. 
      rewrite /splitBallot. simplify.
      rewrite 4! oget_some. rewrite getP_eq. rewrite oget_some.
      progress. rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite 2! negationMul. 
      rewrite 2! FZ_inverse4. rewrite 2! addf0.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite 2! negationMul. 
      rewrite 2! FZ_inverse4. rewrite 2! addf0.
      by smt.

      clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. 
      rewrite /splitBallot. simplify.
      rewrite 4! oget_some. rewrite getP_eq. rewrite oget_some.
      progress. rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite 2! negationMul. 
      rewrite 2! FZ_inverse4. rewrite 2! addf0.
      rewrite 4! pow_pow. rewrite 2! mulC.
      rewrite 4! mul_pow. rewrite 2! negationMul. 
      rewrite 2! FZ_inverse4. rewrite 2! addf0.
      by smt. 

      do(wp; rnd; auto). simplify. progress.
      rewrite fDistrWeight. by trivial. by smt.
  qed.

      
end Voting.