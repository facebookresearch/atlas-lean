# Monadic chosen-ciphertext adversary

Fix a [sampling family](sample-fam.md) and types $M$ of messages and $C$ of ciphertexts. A monadic chosen-ciphertext adversary against a private-key scheme is one computation over the signature whose operations are sampling operations of the family, encryption queries $m \in M$ answered in $C$, and decryption queries $c \in C$ answered in $M \cup \{\bot\}$ (an optional message, $\bot$ for rejection). In its first stage it may use all three at any point, and it returns

- a pair of challenge messages $(m_0, m_1) \in M \times M$, and
- a second stage: a function from the challenge ciphertext $c \in C$ to another computation with the same operations that returns a Boolean guess.

The type does not forbid decrypting the challenge; the [experiment](m-cca-exp.md) does. There is no length condition on $(m_0, m_1)$; a fixed-length message type realizes the equal-length convention of Katz and Lindell, Definition 3.33.
