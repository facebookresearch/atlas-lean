# Supergeneralized Leonardo p-numbers via Fibonacci p-numbers

For all natural numbers
$p \ge 1$, $k$ and $n$ with $n > p$ and every real sequence $x$, the supergeneralized Leonardo
$p$-numbers $\mathcal{L}_{p,k,x}$ and the Fibonacci $p$-numbers $F_p$ satisfy

$$\mathcal{L}_{p,k,x}(n) = F_p(n-p+1)\,x_p + \sum_{i=0}^{\min(p-1,\,n-p-1)} F_p(n-p-i)\,x_i +
\max\Big\{0, \sum_{j=0}^{\lfloor (n-p)/(p+1) \rfloor} \binom{n-p-pj}{j+1}\Big\} \cdot k.$$

This is Corollary 7 of the paper with the factor $k$ restored. The printed corollary omits the
factor $k$ on the last term (and reuses $k$ as the summation index); without it the identity
fails, e.g. at $p = 1$, $k = 2$, $n = 2$, $x = (1, 1)$: $\mathcal{L}_{p,k,x}(n) = 4$ but the
printed right side is $3$. The factor is the one in Theorem 3, of which the corollary is stated
to be an immediate combination with Theorems 4 and 5.

## Sources

- Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2, Corollary 7.
