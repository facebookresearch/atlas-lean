# Real chosen-ciphertext experiment as a function of the coins

On coins $(k, r, \omega_1, x, \omega_2)$ of the hybrid argument and with challenge bit $b$, the real
experiment runs the adversary's first stage with coins $r$ on the tape $\omega_1$ against the real
oracles, encrypts the chosen message $m_b$ with randomness $x$ to get the challenge, and runs the
second stage on the tape $\omega_2$ against the real oracles that reject the challenge. Its output is
the adversary's guess.
