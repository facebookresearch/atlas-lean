# Small-capacity regime of the succinct dictionary

If $n < 2^{\beta(c)}$ for the threshold exponent $\beta(c) = \Theta(c^6)$, a deterministic array of $n$ (present, key, value) triples scanned linearly implements the dynamic dictionary exactly, uses at most $\mathrm{opt}(U, V, n) + (\beta(c) + 2)\, n\, \lambda(n)$ bits with $\lambda(n) = \Theta(\log\log n)$, and takes $O_c(1)$ instructions per operation with zero failure probability.

## Proof sketch

Storing full keys costs $n \lceil \log_2 U \rceil < \lceil \log_2 \binom{U}{n} \rceil + n \lceil \log_2 n \rceil + n$ bits by the power–binomial inequality (the extra $n$ covers rounding), and $n \lceil \log_2 n \rceil \le (\beta(c) + 1)\, n \le (\beta(c)+2)\, n\, \lambda(n)$ because $\log_2 n < \beta(c)$ and $\lambda(n) \ge 1$; scanning $n < 2^{\beta(c)}$ entries is constant time for fixed $c$.

## Depends on

- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Power–binomial inequality](../dictionary-specifications/power-binomial-inequality.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
