# Left-or-right chosen-plaintext experiment

For a private-key encryption scheme, a chosen-plaintext adversary and a bit $b$, the experiment
draws a key $k \leftarrow \mathrm{Gen}$ and the adversary's coins, runs the first stage with the
oracle $\mathrm{Enc}_k$ to get messages $m_0, m_1$, draws the challenge
$c \leftarrow \mathrm{Enc}_k(m_b)$, runs the second stage on $c$ with the same oracle, and outputs
the adversary's guess. Every oracle query is answered with fresh randomness.
