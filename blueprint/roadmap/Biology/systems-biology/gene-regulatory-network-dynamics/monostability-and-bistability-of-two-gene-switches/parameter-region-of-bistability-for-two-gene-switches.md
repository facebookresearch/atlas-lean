# Parameter region of bistability for two-gene switches

**Setting.** The system $\dot x = \alpha f(y) - x$, $\dot y = \beta g(x) - y$ on $\mathbb{R}_+^2$ with $f, g$ both increasing or both decreasing and $\gamma^{1/2}$-convex, at least one strictly (see [$\gamma^{1/2}$-convexity criterion for at most bistability of two-gene switches](gamma-half-convexity-criterion-for-at-most-bistability.md)).

**Theorem (mono/bistability alternative).** Let

$$
E_1^> = \Big\{ (x, y) \in \mathbb{R}_+^2 : \frac{x g'(x)}{g(x)} \cdot \frac{y f'(y)}{f(y)} > 1 \Big\}, \qquad G_1(x, y) = \Big( \frac{x}{f(y)}, \frac{y}{g(x)} \Big).
$$

1. If $(\alpha, \beta) \in G_1(E_1^>)$, the system has exactly three equilibria, of which exactly two are stable (bistable).
2. If $(\alpha, \beta)$ lies outside the closure $\overline{G_1(E_1^>)}$, the system has a unique equilibrium, which is stable (monostable).

More generally, with $E_n$ the set of $n$-tuples of points sharing the same $G_1$-image and $E_n^>$ the subset where every product of elasticities exceeds $1$: if $(\alpha, \beta) \in G_n(E_n^>)$ there are at least $2n + 1$ equilibria; if there are $2n$ or more equilibria then $(\alpha, \beta) \in G_n(E_n^{\ge})$; and $E_n^> = \emptyset$ forces at most $2n - 1$ equilibria for all $(\alpha, \beta)$.

**Corollary (Hill repressors).** For $f(z) = 1/(1 + z^a)$ and $g(z) = 1/(1 + z^b)$ with $a, b \ge 1$, put $\rho = ab$. If $\rho = 1$, i.e. $a = b = 1$, then $E_1^> = \emptyset$ and the switch is monostable for all $\alpha, \beta$. If $\rho > 1$, with $x^- = (\rho - 1)^{-1/b}$, $y^- = (\rho - 1)^{-1/a}$ and $r^-(x) = \big( (1 + x^b)/((\rho - 1) x^b - 1) \big)^{1/a}$,

$$
E_1^> = \{ (x, y) \in (x^-, \infty) \times (y^-, \infty) : y > r^-(x) \},
$$

and the bistable parameter region is its image under $G_1$. Explicit formulas are also given for shifted Hill functions $(1 + \lambda z^a)/(1 + z^a)$, $\lambda \in [0, 1)$, where the threshold becomes $\rho = ab\,\phi(\lambda_1)\phi(\lambda_2) \ge 1$ with $\phi(\lambda) = (1 - \sqrt{\lambda})/(1 + \sqrt{\lambda})$.

## Depends on

- [$\gamma^{1/2}$-convexity criterion for at most bistability of two-gene switches](gamma-half-convexity-criterion-for-at-most-bistability.md)
- [Hill repression function](../../genetic-toggle-switch/hill.md)

## Expansion

A point $(x, y)$ is an equilibrium for the parameters $G_1(x, y)$, and the map $F = \alpha f \circ \beta g$ satisfies $F'(x) = \frac{x g'(x)}{g(x)} \frac{y f'(y)}{f(y)}$ there. So $(x, y) \in E_1^>$ means that $(x,y)$ is an unstable fixed point with $F' > 1$, which, $F$ being bounded and continuous, forces two further fixed points; the three-equilibria bound then gives exactly three. Outside $\overline{G_1(E_1^>)}$ every equilibrium has $F' < 1$, and a counting argument leaves only one. For Hill functions the elasticity product is $\frac{a y^a}{1 + y^a} \frac{b x^b}{1 + x^b}$, which can exceed $1$ only when $ab > 1$.

## Sources

- J. Guilberteau, C. Pouchol, N. Pouradier Duteil, "Monostability and bistability of biological switches", arXiv:2104.04227 (2021): Section 4 (general framework: sets $E_n$, $E_n^>$, $E_n^{\ge}$, maps $G_n$, the $2n+1$ equilibria proposition and its corollary, the mono/bistability alternative theorem, examples with Hill and shifted Hill functions). <https://doi.org/10.48550/arXiv.2104.04227> Published version: Journal of Mathematical Biology 83 (2021) 65, <https://doi.org/10.1007/s00285-021-01687-y>.
