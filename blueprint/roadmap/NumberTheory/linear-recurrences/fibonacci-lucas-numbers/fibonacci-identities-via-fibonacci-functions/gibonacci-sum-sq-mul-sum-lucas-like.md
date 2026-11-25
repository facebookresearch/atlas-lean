# Companion of Melham's sum-of-squares identity for gibonacci sequences

Let
$G : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$, satisfy $G_{j+2} = G_{j+1} + G_j$ for
every integer $j$, and let $F_m$ be the Fibonacci numbers. Then for every natural number $n$ and
every integer $k$ (the sums below are empty when $n = 0$),

$$
6 \Bigl(\sum_{j=0}^{2n-1} G_{j+k}^2\Bigr)
\Bigl(\sum_{j=0}^{2n-1} G_{j+k} (G_{j+k+1} + G_{j+k-1})\Bigr) =
F_{2n}^2 \bigl(G_{k+n-2}^3 (G_{k+n-1} + G_{k+n-3}) + 4 G_{k+n-1}^3 (G_{k+n} + G_{k+n-2}) +
4 G_{k+n}^3 (G_{k+n+1} + G_{k+n-1}) + G_{k+n+1}^3 (G_{k+n+2} + G_{k+n})\bigr).
$$

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Proposition 8 (`jis-2024-24.6.2-prop-8`).
