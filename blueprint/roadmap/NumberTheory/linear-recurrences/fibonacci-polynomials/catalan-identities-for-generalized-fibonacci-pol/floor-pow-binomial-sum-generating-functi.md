# Generating function of the floor-exponent binomial sums

Let $R$ be a commutative ring,
$t \in R$ and $\ell \ge 1$ an integer, and for $n \ge 0$ let
$T_\ell(n; t) = \sum_{i=0}^{n} \binom{n}{i} t^{\lfloor i/\ell \rfloor}$. Then in the ring $R[[x]]$
of formal power series,

$$\Big(\sum_{n \ge 0} T_\ell(n; t)\, x^n\Big) \big((1-x)^\ell - t x^\ell\big)
  = \sum_{k=0}^{\ell-1} \Big(\sum_{i=0}^{k} (-1)^i \binom{i+\ell-k-1}{i}\Big) x^k.$$

So the generating function of the $T_\ell(n; t)$ is this polynomial divided by the series
$(1-x)^\ell - t x^\ell$, which is invertible since its constant term is $1$.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Theorem 4.4 (`fq-2024-florez11012023-thm-4.4`).
