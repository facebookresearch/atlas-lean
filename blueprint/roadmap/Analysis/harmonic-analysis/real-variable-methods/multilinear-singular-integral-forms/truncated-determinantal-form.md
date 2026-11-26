# Truncated determinantal trilinear form

For complex-valued Schwartz functions $f, g, h$ on $\mathbb{R}^2$ and a real number $\varepsilon$, the truncated form of Gressman et al., with $\delta(x + y + z)$ integrated out by $z = -x - y$, is

$$\Lambda_\varepsilon(f, g, h) = \iint_{|\det[1\ 1\ 1;\, x\ y\ z]| > \varepsilon} \frac{f(x)\, g(y)\, h(z)}{\det[1\ 1\ 1;\, x\ y\ z]}\,dx\,dy, \qquad z = -x - y,$$

where $\det[1\ 1\ 1;\, x\ y\ z]$ is the determinant of the $3 \times 3$ matrix with first row $(1, 1, 1)$ and columns $x, y, z \in \mathbb{R}^2$ below it; on $x + y + z = 0$ it equals $3 \det(x, y)$. For $\varepsilon > 0$ the integrand is bounded by $|f(x)\, g(y)\, h(-x-y)| / \varepsilon$, so the integral converges absolutely. The principal value is the limit as $\varepsilon \downarrow 0$.
