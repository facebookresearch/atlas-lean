# Staver's identity for reciprocal binomial sums

For every natural number $n$, the
following identity between rational numbers holds:

$$\sum_{k=0}^{n} \binom{n}{k}^{-1} = \frac{n+1}{2^{n+1}} \sum_{k=1}^{n+1} \frac{2^k}{k}.$$

Both sides satisfy the recurrence $F(n+1) = 1 + \frac{n+2}{2(n+1)} F(n)$ and both equal $1$ at
$n = 0$, so the identity follows by induction on $n$.

## Sources

- <https://cs.uwaterloo.ca/journals/JIS/VOL14/Sprugnoli/sprugnoli4.tex>. Definition lines 115-125. Formula lines 231-236. The left side expands `S_n^(0)`, the sum of reciprocal binomial coefficients. All arithmetic is rational (`Rat` division and inverses); the statement holds for all `n : Nat`, so the edge case `n = 0` is included.
