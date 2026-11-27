# Monadic public-key CCA experiment with a fixed bit

Let $S$ be a public-key encryption scheme with key-pair distribution $\mathrm{Gen}$, randomized encryption $\mathrm{Enc}_{pk}$ and deterministic decryption $\mathrm{Dec}_{sk}$ with values in $M \cup \{\bot\}$; ciphertexts have decidable equality. For a [monadic public-key CCA adversary](mpub-ccaadversary.md) $A$ and a bit $b$, the experiment

1. samples a key pair $(pk, sk) \leftarrow \mathrm{Gen}$;
2. runs the first stage of $A$ on $pk$, answering sampling operations by the sampling family and each decryption query $c$ by $\mathrm{Dec}_{sk}(c)$; it obtains $((m_0, m_1), g)$;
3. samples the challenge $c^* \leftarrow \mathrm{Enc}_{pk}(m_b)$;
4. runs $g(c^*)$ with the same sampling, answering a decryption query $c$ by $\bot$ if $c = c^*$ and by $\mathrm{Dec}_{sk}(c)$ otherwise, and returns its guess.

There is no encryption oracle; the adversary holds $pk$. The result is the distribution of the guess.
