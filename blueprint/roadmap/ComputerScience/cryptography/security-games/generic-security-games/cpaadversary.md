# Chosen-plaintext adversary

A chosen-plaintext adversary against a private-key encryption scheme (Katz and Lindell,
Definition 3.22) draws random coins from a distribution of its own and then runs in two stages,
deterministic given its coins and the oracle's answers. The first stage has access to an encryption
oracle and outputs two challenge messages $m_0, m_1$. The second stage, which may depend on
everything the first stage saw, receives the challenge ciphertext, again has oracle access, and
outputs a guess $b' \in \{0, 1\}$.
