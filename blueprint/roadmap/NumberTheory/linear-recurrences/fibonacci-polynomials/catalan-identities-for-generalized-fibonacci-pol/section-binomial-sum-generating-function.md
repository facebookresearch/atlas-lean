# Generating function of the binomial section sums

Let $R$ be a commutative ring, $t \in R$,
and let $\ell$ and $s$ be natural numbers with $s < \ell$. Put
$T_{\ell,s}(n; t) = \sum_{i=0}^{n} \binom{n}{\ell i + s} t^i$. Then, as formal power series in $x$
over $R$,

$$\Big( \sum_{n \ge 0} T_{\ell,s}(n; t) x^n \Big) \big( (1-x)^\ell - t x^\ell \big) =
\sum_{k=0}^{\ell-1} \Big( \sum_{i=0}^{k} (-1)^i \binom{\ell}{i} \sum_{r=0}^{k} \binom{k-i}{r\ell+s}
t^r \Big) x^k.$$

That is, the generating function of $T_{\ell,s}(n; t)$ is this polynomial divided by
$(1-x)^\ell - t x^\ell$.

The printed numerator in the source has $t^t$, a typo for $t^r$ ($r$ is the summation index), and
the range $s < \ell$ is the one of (4.4). For $s \ge \ell$ the identity fails: for $\ell = 1$,
$s = 1$, $t = 2$ the left side is $x/(1-x)$ and the right side is $0$.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Theorem 4.5 (`fq-2024-florez11012023-thm-4.5`).
