# Rolling-carpet killing strategy for a bistable population

A population density $u(t,x) \in [0,1]$ on the line obeys $\partial_t u - \partial_{xx} u = g(u)$, with a bistable growth term satisfying

$$

g(0) = g(\alpha) = g(1) = 0, \quad g'(0) < 0,\ g'(1) < 0,\ g'(\alpha) > 0, \quad \int_0^1 g(u)\,du > 0 ,

$$

for some $\alpha \in (0,1)$, so the natural travelling wave invades the empty state. Let $\beta \in (\alpha,1)$ be defined by $\int_0^\beta g = 0$. An intervention kills individuals at rate $\mu$ on an interval of length $L$ moving at speed $c \le 0$ (against the invasion), with $-\mu u \le g(u)$. In the moving frame the problem is the travelling wave equation

$$

-c u' - u'' = g(u)\,\mathbf 1_{\{x<0\}\cup\{x>L\}} - \mu\,\mathbf 1_{\{0<x<L\}}\,u, \qquad u(-\infty) = 1,\ u(+\infty) = 0. \tag{$\mathcal P_1$}

$$

**Theorem.** There exist $\Lambda_0 > 0$ and a decreasing bijection $\Lambda : (-\infty, 0] \to [\Lambda_0, +\infty)$ such that:

1. For every $c \le 0$ and $L < \Lambda(c)$, $(\mathcal P_1)$ has no solution; the solution with $u(-\infty) = 1$ also satisfies $u(+\infty) = 1$, so the population recovers behind the carpet.
2. For every $c \le 0$ and $L > \Lambda(c)$, $(\mathcal P_1)$ has a decreasing solution, a wave that pushes the population back at speed $|c|$.
3. If moreover $g$ is convex on $(0,\alpha)$, then at the threshold $L = \Lambda(c)$: for $-2\sqrt{g'(\alpha)} < c \le 0$ a solution exists, with $u'(\Lambda(c)) = 0$ and $\alpha < u(\Lambda(c)) \le \beta$; for $c \le -2\sqrt{g'(\alpha)}$ no solution exists and $\sup_{L > \Lambda(c)} u(L) = \alpha$.

Solutions for larger $L$ lie below solutions for smaller $L$.

## Expansion

Solutions are defined as the supremum of sub-solutions, which makes them monotone in $L$: a solution for $L_*$ is a super-solution for every $L > L_*$. For fixed $c < 0$ a phase-plane argument on the killing interval (where the equation is linear) and outside it (where the energy $\tfrac12 u'^2 + G(u)$ is controlled) shows existence for $L$ large, and $\Lambda(c)$ is the infimum of admissible lengths. The condition at the exit point $x = L$ is that the trajectory must reach the stable manifold of $0$; when $|c|$ exceeds $2\sqrt{g'(\alpha)}$ the linearisation at $\alpha$ has real eigenvalues and the limiting trajectory gets stuck at $\alpha$.

## Sources

- Luis Almeida, Alexis Leculier, Nicolas Vauchelet, "Analysis of the 'Rolling carpet' strategy to eradicate an invasive species", arXiv (2021); SIAM Journal on Mathematical Analysis (2023). Theorem 1 and Section 2 (Propositions 1–3). <https://doi.org/10.48550/arXiv.2106.11252>. Published version: SIAM Journal on Mathematical Analysis 55(1) (2023), 275–309, <https://doi.org/10.1137/21m1427243>; locators above refer to the arXiv version.
