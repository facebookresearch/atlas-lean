# Monadic CCA experiment with a fixed bit

Let $S$ be a private-key encryption scheme with key distribution $\mathrm{Gen}$, randomized encryption $\mathrm{Enc}_k$ and deterministic decryption $\mathrm{Dec}_k$ with values in $M \cup \{\bot\}$. Ciphertexts have decidable equality. For a [monadic CCA adversary](mccaadversary.md) $A$ and a bit $b$, the experiment

1. samples a key $k \leftarrow \mathrm{Gen}$;
2. runs the first stage of $A$, answering sampling operations by the sampling family, each encryption query $m$ by a fresh sample of $\mathrm{Enc}_k(m)$, and each decryption query $c$ by $\mathrm{Dec}_k(c)$; it obtains $((m_0, m_1), g)$;
3. samples the challenge $c^* \leftarrow \mathrm{Enc}_k(m_b)$;
4. runs $g(c^*)$ with the same sampling and encryption oracle, answering a decryption query $c$ by $\bot$ if $c = c^*$ and by $\mathrm{Dec}_k(c)$ otherwise, and returns its guess.

The result is the distribution of the guess; the [game](m-cca-game.md) tests it against $b$.
