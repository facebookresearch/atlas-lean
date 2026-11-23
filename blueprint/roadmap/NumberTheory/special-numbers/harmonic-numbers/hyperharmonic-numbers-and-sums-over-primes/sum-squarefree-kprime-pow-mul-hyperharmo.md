# Mixed hyperharmonic product sums over squarefree numbers with $k$ prime factors

Let
$q_1 \ge 2$ and $q_2, \alpha, \beta, m, k, s, n, r_1, r_2 \ge 1$ be natural numbers. Let
$p_{\ell,k}$ be the $\ell$th ($\ell \ge 1$) squarefree number with exactly $k$ prime factors.
Write $H_\ell^{(q)} = \sum_{j=1}^{\ell} j^{-q}$ and
$\bar H_\ell^{(q)} = \sum_{j=1}^{\ell} (-1)^{j-1} j^{-q}$; let $H_\ell^{(q,1)} = H_\ell^{(q)}$ and
$H_\ell^{(q,r+1)} = \sum_{j=1}^{\ell} H_j^{(q,r)}$, and define $H_\ell^{(q,r,2)}$ by the same
recursion from $H_\ell^{(q,1,2)} = \bar H_\ell^{(q)}$. Let $h_\ell^{(t)}$ be the hyperharmonic
numbers, $h_\ell^{(0)} = 1/\ell$ and $h_\ell^{(t+1)} = \sum_{j=1}^{\ell} h_j^{(t)}$. Let
$\zeta(q) = \sum_{i \ge 1} i^{-q}$ for $q \ge 2$, and let $\bar\zeta(q_2)$ be $\log 2$ if
$q_2 = 1$ and $(1 - 2^{1-q_2}) \zeta(q_2)$ otherwise. Put
$f(\ell) = p_{\ell,k}^{\alpha} (H_\ell^{(q_1,r_1)})^m (h_\ell^{(s)})^n
(H_\ell^{(q_2,r_2,2)})^\beta$,
$E = m(r_1 - 1) + n(s - 1) + \beta(r_2 - 1)$, $A = \alpha + E + 1$,
$D = ((r_1 - 1)!)^m ((s - 1)!)^n ((r_2 - 1)!)^\beta$ and $Z = \zeta(q_1)^m \bar\zeta(q_2)^\beta$.
Then, as the natural number $x$ tends to infinity,

$$\sum_{\ell=1}^{x} f(\ell) \sim
\frac{((k-1)!)^\alpha Z x^A (\log x)^{\alpha+n}}{A D (\log\log x)^{\alpha(k-1)}}$$

and

$$\sum_{1 \le \ell \le x,\ p_{\ell,k} \le x} f(\ell) \sim
\frac{Z x^A (\log\log x)^{(E+1)(k-1)}}{A D ((k-1)!)^{E+1}
(\log x)^{m(r_1-1)+n(s-2)+\beta(r_2-1)+1}}.$$

The exponent of $\log x$ in the second formula is an integer, which is negative for some
parameters with $s = 1$.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Theorem 15 (`jis-2024-24.4.1-thm-15`).
