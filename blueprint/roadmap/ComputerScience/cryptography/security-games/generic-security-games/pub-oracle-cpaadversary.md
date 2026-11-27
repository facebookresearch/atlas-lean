# Chosen-plaintext adversary against public-key encryption

A chosen-plaintext adversary against a public-key encryption scheme, with an encryption oracle
(Katz and Lindell, Section 11.2.2), draws random coins from a distribution of its own and runs in
two stages. The first stage sees the public key $pk$, has access to the oracle $\mathrm{Enc}_{pk}$,
and outputs two challenge messages $m_0, m_1$. The second stage, which may depend on everything the
first stage saw, receives the challenge ciphertext, again has oracle access, and outputs a guess.
