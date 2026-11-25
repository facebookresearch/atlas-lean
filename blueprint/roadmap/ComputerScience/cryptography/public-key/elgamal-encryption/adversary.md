# ElGamal eavesdropping adversary

Given a type $G$ of public keys and messages and a type
$R$ of random coins, an eavesdropping adversary consists of a choice function, which maps a public
key $h \in G$ and coins $r \in R$ to a pair of messages in $G \times G$, and a guessing function,
which maps a public key $h \in G$, a ciphertext in $G \times G$ and coins $r \in R$ to a bit.
