# Persistence–extinction dichotomy under accessibility

For the monotone stochastic matrix model $X_{t+1} = A(X_t,\xi_{t+1})X_t$ with positive density dependence and standing assumptions A1–A5, call $\{0,\infty\}$ accessible if for every $c > 0$ there is $\gamma > 0$ such that, from every $x \gg 0$, with probability at least $\gamma$ the population at some time satisfies $X_t \gg c\mathbf{1}$ or $X_t \ll \mathbf{1}/c$.

**Theorem.** If $r_0 < 0 < r_\infty$ and $\{0,\infty\}$ is accessible, then for every initial condition $x$

$$ \mathbb{P}\Big[\lim_{t\to\infty} \|X_t\| = \infty \ \text{ or } \ \lim_{t\to\infty} X_t = 0 \,\Big|\, X_0 = x\Big] = 1 , $$

so the population either goes extinct or grows without bound, and no positive stationary behavior exists. Together with the dependency's theorem this gives the trichotomy: extinction with probability one ($r_\infty < 0$), persistence with probability one ($r_0 > 0$), or, for $r_0 < 0 < r_\infty$, for every $\varepsilon > 0$ thresholds $c^* > c_* > 0$ with $\mathbb{P}[X_t \to 0 \mid X_0 = x] \ge 1-\varepsilon$ for $x \le c_*\mathbf{1}$ and $\mathbb{P}[\|X_t\| \to \infty \mid X_0 = x] \ge 1-\varepsilon$ for $x \ge c^*\mathbf{1}$.

The source's abstract also says that each outcome then has positive probability from positive initial conditions; that does not follow and is false: $A(x,\xi) = h(x)\xi$ with $h(x) = 0.5 + 1.5\min(x,1)$ and $\xi$ uniform on $[0.9,1.1]$ satisfies A1–A5 and accessibility, yet from $x \ge 1$ extinction has probability $0$.

## Depends on

- [Dynamical trichotomy for positively density-dependent stochastic matrix models](dynamical-trichotomy-for-positively-density-dependent-stochastic-matrix-models.md)

## Expansion

Accessibility lets the environment push any trajectory, with probability bounded below, into a neighborhood of $0$ or of $\infty$ where the local results give convergence with probability at least $1-\varepsilon$. A standard argument over repeated attempts then shows that the event of neither converging to $0$ nor escaping to infinity has probability zero. The scalar version of this trichotomy is due to Roth and Schreiber.

## Sources

- Sebastian J. Schreiber, "A Dynamical Trichotomy for Structured Populations Experiencing Positive Density-Dependence in Stochastic Environments", in Springer Proceedings in Mathematics & Statistics (2017), 55–66, <https://doi.org/10.1007/978-981-10-6409-8_3>. Published version of arXiv:1701.08443, cited next; locators there refer to the arXiv version.
- S. J. Schreiber, "A dynamical trichotomy for structured populations experiencing positive density-dependence in stochastic environments", arXiv:1701.08443 (2017), Section 3, Theorem 3.2 and the definition of accessibility, Section 4 (spatial and age-structured applications) and Section 5 (proofs). <https://doi.org/10.48550/arXiv.1701.08443>
