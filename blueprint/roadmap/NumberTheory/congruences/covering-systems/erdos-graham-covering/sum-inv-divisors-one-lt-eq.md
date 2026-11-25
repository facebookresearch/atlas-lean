# Sum of the reciprocals of the divisors greater than one

For every natural number $n \ge 1$, in the rationals,

$$\sum_{\substack{d \mid n \\ d > 1}} \frac{1}{d} = -1 + \sum_{d \mid n} \frac{1}{d}
= -1 + \prod_{p \mid n} \sum_{j=0}^{v_p(n)} \frac{1}{p^j},$$

where the product runs over the primes $p$ dividing $n$ and $v_p(n)$ is the exponent of $p$ in $n$.

## Sources

- Sarosh Adenwalla, "A Question of Erdős and Graham on Covering Systems", INTEGERS 26 (2026), Article A52, Proposition 2.3 (folklore).
