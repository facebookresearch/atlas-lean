# Weighted count of primes in the $\ell$-numerical semigroup

For every natural number
$\ell$ and every $\varepsilon > 0$ there is a natural number $C$ such that the following holds
for all coprime natural numbers $c$ and $d$ with $C \le c < d$. For a natural number $k$ put
$g_k(c, d) = (k + 1)cd - c - d$, so that $g_0(c, d) = cd - c - d$, and let $\psi_{\ell,c,d}$ be
the sum of the von Mangoldt function $\Lambda(n)$ over the natural numbers $n$ with
$\ell cd < n \le g_\ell(c, d)$ of the form $n = \ell cd + cx_0 + dy_0$ for some natural numbers
$x_0 \le d$ and $y_0 \le c$. Then

$$
\left|\psi_{\ell,c,d} - \frac{g_0(c, d)}{2}\right| < \varepsilon \, \frac{g_0(c, d)}{2}.
$$

That is, $\psi_{\ell,c,d} \sim g_0(c, d)/2$ as $c \to \infty$, uniformly over coprime $d > c$.

## Sources

- Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and Skałba, III*, INTEGERS 25 (2025), Article A51, Proposition 1 (`integers-2025-A51-prop-1`), with `g_ℓ(c, d)` from equation (1).
