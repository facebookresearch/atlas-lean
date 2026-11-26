# Left-or-right chosen-ciphertext experiment

For a private-key encryption scheme, a chosen-ciphertext adversary and a bit $b$, the experiment
draws a key $k \leftarrow \mathrm{Gen}$ and the adversary's coins, runs the first stage with the
encryption and decryption oracles for $k$ to get messages $m_0, m_1$, draws the challenge
$c^* \leftarrow \mathrm{Enc}_k(m_b)$, runs the second stage on $c^*$ with oracles that answer $\bot$
to a decryption query for $c^*$, and outputs the adversary's guess.
