# uvoting
EasyCrypt model of a voting protocol that was used in 2016.


# Installation instructions 

Installation instructions for EasyCrypt can be found from: https://www.easycrypt.info/trac/browser/README.md?rev=1.0. 


1. Installing required packages for Ubuntu 16.04:
	- apt update
	- apt install ocaml ocaml-native-compilers camlp4-extra opam
	- apt install emacs24
	- apt install m4


2. Installing EasyCrypt and its dependencies. Our code works with EasyCrypt's git commit a8c2c61a3bc7195fc4fcd5e7241d931d037dd803. 
	- opam init
	- eval \`opam config env\`
	- opam repository add easycrypt git://github.com/EasyCrypt/opam.git
	- opam pin -n add easycrypt https://github.com/EasyCrypt/easycrypt.git#a8c2c61a3bc7195fc4fcd5e7241d931d037dd803
	- opam update
	- opam install depext
	- opam depext easycrypt
	- opam install easycrypt
	- opam depext conf-autoconf.0.1
	- opam install ec-provers
	- opam install proofgeneral


3. Why3 has to be configured to make smt work in EasyCrypt:
	- why3 config --detect


4. Optional: 
EasyCrypt's interactive mode is built with ProofGeneral. Instructions for configuring ProofGeneral can be found from: https://www.easycrypt.info/trac/browser/README.md?rev=1.0


5. Unpack the source code of the voting protocol and navigate to the corresponding directory. 


6. To verify the voting protocol code in non-interactive mode: 
	- easycrypt voting.ec


7. To verify the voting protocol code in interactive mode (requires step 4):
	- emacs voting.ec
	- ctrc + c ctrl + b
