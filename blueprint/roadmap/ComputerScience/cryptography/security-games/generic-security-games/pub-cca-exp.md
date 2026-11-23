# Left-or-right public-key chosen-ciphertext experiment

For a public-key encryption scheme, a chosen-ciphertext adversary and a bit $b$, the experiment draws
$(pk, sk) \leftarrow \mathrm{Gen}$ and the adversary's coins, runs the first stage on $pk$ with the
decryption oracle for $sk$ to get $m_0, m_1$, draws the challenge
$c^* \leftarrow \mathrm{Enc}_{pk}(m_b)$, runs the second stage on $c^*$ with a decryption oracle that
answers $\bot$ on $c^*$, and outputs the adversary's guess.
