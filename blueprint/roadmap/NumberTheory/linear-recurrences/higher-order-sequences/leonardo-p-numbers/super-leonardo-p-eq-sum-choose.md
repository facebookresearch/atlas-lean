# Explicit formula for the supergeneralized Leonardo p-numbers

For all natural numbers
$p \ge 1$, $k$ and $n$ with $n > p$ and every real sequence $x$, the supergeneralized Leonardo
$p$-numbers $\mathcal{L}_{p,k,x}$ satisfy

$$\mathcal{L}_{p,k,x}(n) =
\Big(\sum_{i=0}^{\lfloor (n-p)/(p+1) \rfloor} \binom{n-p-ip}{i}\Big) x_p +
\sum_{i=0}^{\min(p-1,\,n-p-1)} \Big(\sum_{j=0}^{\lfloor (n-p-i-1)/(p+1) \rfloor}
\binom{n-p-i-1-jp}{j}\Big) x_i +
\max\Big\{0, \sum_{j=0}^{\lfloor (n-p)/(p+1) \rfloor} \binom{n-p-pj}{j+1}\Big\} \cdot k.$$

This is Theorem 9 of the paper with the factor $k$ restored: as in Corollary 7, the printed
theorem omits the factor $k$ on the last term and is false without it (same counterexample:
$p = 1$, $k = 2$, $n = 2$, $x = (1, 1)$ gives $4$ versus $3$).

## Sources

- Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2, Theorem 9.
