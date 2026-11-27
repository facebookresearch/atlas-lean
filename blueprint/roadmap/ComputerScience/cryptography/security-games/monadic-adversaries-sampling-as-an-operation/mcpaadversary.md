# Monadic chosen-plaintext adversary

Fix a [sampling family](sample-fam.md) and types $M$ of messages and $C$ of ciphertexts. A monadic chosen-plaintext adversary is one computation over the encryption-oracle signature (queries $m \in M$ answered in $C$) extended by the sampling operations of the family. In its first stage it may sample and query encryption at any point, and it returns

- a pair of challenge messages $(m_0, m_1) \in M \times M$, and
- a second stage: a function from the challenge ciphertext $c \in C$ to another computation of the same kind (again able to sample and query encryption) that returns a Boolean guess.

The structure imposes no length condition on $(m_0, m_1)$. A fixed-length message type realizes the equal-length convention of Katz and Lindell, Definition 3.22. This is the monadic form of the coin CPA adversary, which instead receives all its randomness up front.
