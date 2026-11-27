# Separatrix of the strong-competition Lotka–Volterra system

Consider the nondimensional two-species competition model for a native population $x$ and an invader $y$,

$$
\dot x = x(1 - x - \alpha y), \qquad \dot y = \delta\, y (1 - y - \beta x),
$$

in the strong competition regime $\alpha, \beta > 1$, with relative growth rate $\delta > 0$. Its equilibria in $\mathbb{R}^2_+$ are the unstable node $P_0 = (0,0)$, the stable nodes $P_N = (1,0)$ and $P_I = (0,1)$, and the saddle $P_C = (A,B)$ with

$$
A = \frac{\alpha - 1}{\alpha\beta - 1}, \qquad B = \frac{\beta - 1}{\alpha\beta - 1}.
$$

The system has no limit cycles and every trajectory in $\mathbb{R}^2_+$ converges to an equilibrium. Let $S$ be the stable invariant curve of the saddle $P_C$ (the set of initial states converging to $P_C$) and $\hat S = S \cup \{P_0\}$.

**Theorem.**

1. $S$ is the separatrix between the basins of $P_N$ and $P_I$. $\hat S$ is the graph of a smooth, strictly increasing function $y = s(x)$, $x \ge 0$, with $s(0) = 0$; initial states with $y_0 < s(x_0)$ converge to $P_N$ and those with $y_0 > s(x_0)$ converge to $P_I$. The left branch of $S$ is a heteroclinic connection from $P_0$ to $P_C$.
2. $s$ satisfies the integral equation

$$
s(x) = s^*(x) \exp\left( \delta \int_A^x \frac{(\beta - 1) s(\bar x) - (\alpha - 1)\bar x}{\bar x (1 - \bar x - \alpha s(\bar x))}\, d\bar x \right), \qquad s^*(x) = B \left(\frac{x}{A}\right)^{\delta},
$$

and $s^*$ is a uniform approximation of $s$ that is exact when $\delta = 1$.
3. For fixed $x > 0$: $s$ is strictly decreasing in $\alpha$, strictly increasing in $\beta$, and strictly decreasing in $\delta$ for $x < A$ but strictly increasing for $x > A$.
4. As $\delta \to 0$, $\hat S \to \{P_0\} \cup \{(x, B) : x > 0\}$; as $1/\delta \to 0$, $\hat S \to \{P_0\} \cup \{(A, y) : y > 0\}$.

Consequently, the **precariousness** of a native density $x_0$ (the minimal invader density that drives the system into the basin of $P_I$) equals $s(x_0)$.

## Expansion

The tangent to $S$ at the saddle has positive slope $m = (\sqrt{\Delta} - \eta)/(2\alpha(\alpha - 1))$, where $\Delta = \kappa^2 + 4\delta(\alpha-1)(\beta-1)(\alpha\beta-1)$, $\kappa = (\alpha-1) + \delta(\beta-1)$, $\eta = (\alpha-1) - \delta(\beta-1)$. The rectangles $(0,A)\times(0,B)$ and $(A,\infty)\times(B,\infty)$ are negatively invariant and both vector field components have fixed signs there, so the two branches of $S$ stay in them and are graphs of increasing functions. Writing the orbit equation $dy/dx = \delta y (1-y-\beta x)/(x(1-x-\alpha y))$ as a perturbation of the exactly solvable $\delta = 1$ case yields the integral equation; differentiating it in the parameters gives the monotonicity statements.

## Sources

- Artur César Fassoni, Denis Carvalho Braga, "Resilience Analysis for Competing Populations", Bulletin of Mathematical Biology 81 (2019), 3864–3888, <https://doi.org/10.1007/s11538-019-00660-7>. Published version of arXiv:1903.06291, cited next; locators there refer to the arXiv version.
- Artur César Fassoni, Denis de Carvalho Braga, "Resilience Analysis for Competing Populations", arXiv (2019). Theorem 1, Proposition 1, Proposition 2, Lemma 1, Lemma 2, Theorem 2, Lemma 4. <https://doi.org/10.48550/arXiv.1903.06291>
