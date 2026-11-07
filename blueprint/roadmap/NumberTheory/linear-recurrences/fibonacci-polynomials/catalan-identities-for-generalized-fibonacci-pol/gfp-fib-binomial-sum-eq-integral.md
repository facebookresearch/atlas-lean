# Binomial sum of generalized Fibonacci polynomials as an integral

Let $d$ and $g$ be
polynomials with integer coefficients, let $F_m$ be the generalized Fibonacci polynomials with
$F_0 = 0$, $F_1 = 1$ and $F_{m+2} = d F_{m+1} + g F_m$, and let $x$ be a real number with
$d(x)^2 + 4 g(x) \ge 0$ and $g(x) \ne 0$. Let $\Phi \colon \mathbb{Z} \to \mathbb{R}$ satisfy
$\Phi(m) = F_m(x)$ for $m \ge 0$ and $\Phi(m+2) = d(x) \Phi(m+1) + g(x) \Phi(m)$ for every integer
$m$. Then for every real $k \ge 2$ and every integer $n \ge 1$,

$$\sum_{i=0}^{n} (-1)^{n+1} \binom{n}{i} (k+1)^i (k-1)^{n-i} g(x)^i \, \Phi(n-2i)
  = n \int_{-k}^{k} \Big(y \sqrt{d(x)^2 + 4 g(x)} + d(x)\Big)^{n-1} dy.$$

The extension $\Phi$ of $m \mapsto F_m(x)$ to negative indices exists only when $g(x) \ne 0$: if
$g(x) = 0$, the recurrence at $m = -1$ forces $F_1(x) = d(x) F_0(x) = 0$.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Proposition 5.2 (`fq-2024-florez11012023-prop-5.2`).
