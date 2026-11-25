# Triangular $q$-binomial coefficients via Gaussian binomials

For natural numbers $r$ and
$s$ with $1 \le r$ and $s \le r$, the triangular $q$-binomial coefficient $t[r, s]$ satisfies

$$
t[r, s] = q^s \binom{r + s - 1}{s}_q - q^{s+1} \sum_{i=2}^{s} t[i - 1, i - 1] \,
q^{i(r - i)} \binom{r + 1 + s - 2i}{s - i}_q
$$

in $\mathbb{Z}[[q]]$, where $\binom{M}{k}_q$ denotes the Gaussian binomial coefficient.

In the range $s \le r$ every exponent and binomial index above is a natural number; for $s > r$
one has $t[r, s] = 0$.

## Sources

- Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*, INTEGERS 24 (2024), Article A56, Proposition 4, eq. (12).
