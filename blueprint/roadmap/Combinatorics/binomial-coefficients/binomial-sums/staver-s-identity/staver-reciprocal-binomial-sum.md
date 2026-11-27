# Staver's identity for reciprocal binomial sums

For every natural number $n$, the
following identity between rational numbers holds:

$$\sum_{k=0}^{n} \binom{n}{k}^{-1} = \frac{n+1}{2^{n+1}} \sum_{k=1}^{n+1} \frac{2^k}{k}.$$

Both sides satisfy the recurrence $F(n+1) = 1 + \frac{n+2}{2(n+1)} F(n)$ and both equal $1$ at
$n = 0$, so the identity follows by induction on $n$.

## Sources

- Renzo Sprugnoli, *Moments of Reciprocals of Binomial Coefficients*, J. Integer Seq. 14 (2011), Article 11.7.8, Theorem 6 (the left side is the number $S_n^{(0)}$ there), <https://cs.uwaterloo.ca/journals/JIS/VOL14/Sprugnoli/sprugnoli4.tex>.
