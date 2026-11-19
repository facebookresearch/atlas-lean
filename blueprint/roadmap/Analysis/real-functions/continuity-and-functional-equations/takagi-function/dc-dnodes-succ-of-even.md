# Successor formula for the D-node count at even arguments

Let $\delta$ be the
divide-and-conquer D-node count and $s_1(n)$ the number of ones in the binary expansion of $n$.
For every even integer $n > 0$, $\delta(n+1) = \delta(n) + \lfloor \log_2 n \rfloor - 2 s_1(n) + 2$.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Lemma 19 (`jis-2024-24.2.7-lem-19`).
