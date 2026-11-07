# Gamma representation of generalized harmonic numbers

Let $s > 0$ be real, let
$H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ denote the generalized harmonic numbers, and let $X_s$ be a
random variable with the Gamma distribution $\mathrm{Gamma}(s, 1)$ of shape $s$ and rate $1$. Then
for every natural number $n$,

$$H_n^{(s)} = \sum_{k=0}^{n-1} \mathbb{E}[e^{-k X_s}] =
\mathbb{E}\left[\frac{1 - e^{-n X_s}}{1 - e^{-X_s}}\right].$$

## Sources

- Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 1, Equation (5) (`integers-2026-A124-lem-1`).
