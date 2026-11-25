# Left-or-right public-key chosen-plaintext experiment

For a public-key encryption scheme, a chosen-plaintext adversary with an encryption oracle and a bit
$b$, the experiment draws $(pk, sk) \leftarrow \mathrm{Gen}$ and the adversary's coins, runs the first
stage on $pk$ with the oracle $\mathrm{Enc}_{pk}$ to get $m_0, m_1$, draws the challenge
$c \leftarrow \mathrm{Enc}_{pk}(m_b)$, runs the second stage on $c$ with the same oracle, and outputs
the adversary's guess.
