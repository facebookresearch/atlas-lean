# Whitt's generalized Catalan numbers

For a rational number $\alpha$ and a natural number
$n$, Whitt's generalized Catalan number $C(\alpha, n)$ is the rational number

$$C(\alpha, n) = \sum_{k=0}^{n-1} \left(1 - \frac{k}{n}\right) \binom{n-1+k}{k} \alpha^k.$$

In particular $C(\alpha, 0) = 0$, the empty sum. Writing $n + 1$ for $n$ gives the source's form
$C(\alpha, n+1) = \sum_{k=0}^{n} \left(1 - \frac{k}{n+1}\right) \binom{n+k}{k} \alpha^k$. For
$\alpha = 2$ and $n \ge 1$ these are the terms of OEIS A064062.

## Sources

- Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026), Article A27, Section 5 (definition of `C(α, n+1)`, quoting W. Whitt, J. Integer Seq. 14 (2011)).
