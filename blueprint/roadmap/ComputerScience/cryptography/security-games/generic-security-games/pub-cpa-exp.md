# Left-or-right public-key eavesdropping experiment

For a public-key encryption scheme, an eavesdropping adversary and a bit $b$, the experiment draws a
key pair $(pk, sk) \leftarrow \mathrm{Gen}$ and the adversary's coins $r$, lets the adversary choose
$m_0, m_1$ from $pk$ and $r$, draws the challenge $c \leftarrow \mathrm{Enc}_{pk}(m_b)$, and outputs
the adversary's guess from $pk$, $c$ and $r$.
