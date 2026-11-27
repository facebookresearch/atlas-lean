# Monadic CPA experiment with a fixed bit

Let $S$ be a private-key encryption scheme with key distribution $\mathrm{Gen}$, randomized encryption $\mathrm{Enc}_k$ and deterministic decryption $\mathrm{Dec}_k$ with values in $M \cup \{\bot\}$. For a [monadic CPA adversary](mcpaadversary.md) $A$ and a bit $b$, the experiment

1. samples a key $k \leftarrow \mathrm{Gen}$;
2. runs the first stage of $A$, answering sampling operations by the sampling family and each encryption query $m$ by a fresh sample of $\mathrm{Enc}_k(m)$, and obtains $((m_0, m_1), g)$;
3. samples the challenge $c \leftarrow \mathrm{Enc}_k(m_b)$;
4. runs $g(c)$ with the same sampling and encryption oracle and returns its guess.

The result is the distribution of the guess, not of whether it equals $b$; the [game](m-cpa-game.md) adds that test.
