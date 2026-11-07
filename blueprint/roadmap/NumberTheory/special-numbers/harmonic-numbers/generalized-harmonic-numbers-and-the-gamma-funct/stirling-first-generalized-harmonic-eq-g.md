# Gamma representation of the Stirling combination of generalized harmonic numbers

Let
$s > 0$ be real and let $X_s$ be a random variable with the Gamma distribution
$\mathrm{Gamma}(s, 1)$ of shape $s$ and rate $1$. Write $[a, b]$ for the unsigned Stirling number
of the first kind, the number of permutations of $a$ elements with exactly $b$ cycles, and, for
real $t$ and a natural number $n$, write $H_n^{(t)} = \sum_{k=1}^{n} 1/k^t$ for the generalized
harmonic number. Then for all natural numbers $m$ and $n$,

$$\frac{1}{(m+1)!} \sum_{j=0}^{m+1} [m+1, j] (-1)^{m+1-j} H_n^{(s-j)} =
\sum_{k=0}^{n-1} \binom{k+1}{m+1} \mathbb{E}[e^{-k X_s}].$$

The source assumes $s > m + 1$; the identity holds for every $s > 0$.

## Sources

- Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Corollary 1, Equation (8).
