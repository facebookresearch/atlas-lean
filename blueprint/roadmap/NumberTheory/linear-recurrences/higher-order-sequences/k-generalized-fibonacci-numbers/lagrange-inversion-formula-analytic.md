# Lagrange inversion formula

Let $f, g : \mathbb{C} \to \mathbb{C}$ be analytic at $z_0$.
There are $\varepsilon > 0$ and $\delta > 0$ such that for every $\alpha \in \mathbb{C}$ with
$|\alpha| < \delta$ the equation $w = z_0 + \alpha f(w)$ has exactly one solution $w$ with
$|w - z_0| < \varepsilon$, and for this solution the series
$\sum_{n \ge 1} \frac{\alpha^n}{n!} \frac{d^{n-1}}{dz^{n-1}} \bigl(f(z)^n g'(z)\bigr)\big|_{z=z_0}$
converges absolutely to $g(w) - g(z_0)$.

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 1 (`jis-2024-24.1.1-thm-1`).
