# Monadic public-key chosen-ciphertext adversary

Fix a [sampling family](sample-fam.md), types $M$ of messages and $C$ of ciphertexts, and a type $PK$ of public keys. A monadic chosen-ciphertext adversary against a public-key scheme maps each public key $pk$ to a computation whose operations are sampling operations of the family and decryption queries $c \in C$ answered in $M \cup \{\bot\}$. There is no encryption oracle; the adversary holds $pk$. Its first stage returns

- a pair of challenge messages $(m_0, m_1) \in M \times M$, and
- a second stage: a function from the challenge ciphertext $c \in C$ to another computation with the same operations that returns a Boolean guess.

The type does not forbid decrypting the challenge; the [experiment](m-pub-cca-exp.md) does. There is no length condition on $(m_0, m_1)$ (Katz and Lindell, Definition 11.8). All of the message, ciphertext, tag or signature types and the sampling outcomes live in one universe; the public-key type may live in another.
