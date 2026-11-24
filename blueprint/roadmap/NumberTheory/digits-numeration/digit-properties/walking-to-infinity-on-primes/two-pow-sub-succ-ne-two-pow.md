# A power of two minus a much smaller positive number is not a power of two

Let $p$
and $k$ be natural numbers with $k \ge \lceil \log_2 (p + 1) \rceil + 2$. Then $2^k - (p + 1)$
is not a power of $2$: there is no natural number $m$ with $2^k - (p + 1) = 2^m$.

Under this hypothesis $2^k > p + 1$, so the subtraction is exact. The source assumes $p$ is
prime; the statement holds without that assumption.

## Sources

- Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024), Article A78, Lemma 2.5.
