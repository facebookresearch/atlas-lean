# Raikov's Tauberian theorem

Let $a_1, a_2, \ldots$ be nonnegative real numbers whose
Dirichlet series $F(s) = \sum_{n \ge 1} a_n n^{-s}$ converges absolutely for $\mathrm{Re}\, s > 1$,
and let $\alpha < 1$ be real. Suppose that $H$ is a function holomorphic on an open set containing
the half-plane $\mathrm{Re}\, s \ge 1$ and nonzero on that half-plane, and that
$F(s) = H(s) / (s - 1)^{1 - \alpha}$ for $\mathrm{Re}\, s > 1$, with the principal branch of the
power. Then

$$\sum_{n=1}^{x} a_n \sim \frac{H(1)}{\Gamma(1 - \alpha)} \cdot \frac{x}{(\ln x)^\alpha}$$

as the natural number $x$ tends to infinity.

The paper allows any real $\alpha$; for $\alpha = 1$ the statement fails: $a_1 = 1$, $a_n = 0$
otherwise and $H = 1$ give $F = 1 = H / (s - 1)^0$, but $\Gamma$ has a pole at $0$ and
$\sum_{n \le x} a_n = 1$. The analytic continuation of $F$ across $\mathrm{Re}\, s = 1$,
$s \neq 1$, assumed in the paper, follows from the representation through $H$.

## Sources

- Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 1 (`integers-2025-A75-thm-1`).
