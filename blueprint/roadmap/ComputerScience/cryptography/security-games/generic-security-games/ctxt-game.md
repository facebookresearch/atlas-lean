# Ciphertext integrity

The ciphertext-integrity experiment (INT-CTXT of Bellare and Namprempre; the ciphertext form of the
unforgeable encryption of Katz and Lindell, Section 4.5) draws a key $k \leftarrow \mathrm{Gen}$ and
runs the forger with the oracle $\mathrm{Enc}_k$. The forger outputs a ciphertext $c$ and wins when
$\mathrm{Dec}_k(c) \neq \bot$ and $c$ was never an answer of the oracle.
