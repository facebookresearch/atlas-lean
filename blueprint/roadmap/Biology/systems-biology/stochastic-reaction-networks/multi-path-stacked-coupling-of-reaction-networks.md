# Multi-path stacked coupling of reaction networks

**Setting.** Let $X^{(0)}, \dots, X^{(M)}$ be stochastic reaction networks on $\mathbb{Z}^d_{\ge 0}$ sharing reaction channels $\ell = 1, \dots, R$ with reaction vectors $\zeta_\ell$, but with possibly different intensities $\lambda^{(m)}_\ell$ (for example, the same network at parameter values $\theta_0, \dots, \theta_M$, as needed for finite-difference sensitivity estimators of $\partial_\theta\, \mathbb{E} f(X^\theta(T))$).

- The **split coupling** of two such processes $X^{(i)}, X^{(j)}$ uses independent unit-rate Poisson processes per channel: the pair jumps together by $(\zeta_\ell, \zeta_\ell)$ at rate $\lambda^{(i)}_\ell \wedge \lambda^{(j)}_\ell$, and each coordinate alone jumps by $\zeta_\ell$ at its excess rate $\lambda^{(m)}_\ell - \lambda^{(i)}_\ell \wedge \lambda^{(j)}_\ell$.
- The **multi-path stacked coupling** (MSC) drives all $M+1$ processes by one Poisson point process in time-height space. At time $t$ the height axis is cut into consecutive blocks, block $\ell$ of height equal to the envelope $\bar\lambda_\ell(t) = \max_m \lambda^{(m)}_\ell(X^{(m)}(t))$; a point at relative height $u$ inside block $\ell$ makes exactly those processes $m$ with $u < \lambda^{(m)}_\ell(X^{(m)}(t))$ fire reaction $\ell$.

**Statement.**

1. (Pairwise marginals.) For distinct $i, j$, if the split-coupled pair and the MSC marginal pair $(X^{(i)}_{\mathrm{MSC}}, X^{(j)}_{\mathrm{MSC}})$ are nonexplosive and start from the same joint law, then $(X^{(i)}_{\mathrm{MSC}}, X^{(j)}_{\mathrm{MSC}}) \overset{d}{=} (X^{(i)}_{\mathrm{SC}}, X^{(j)}_{\mathrm{SC}})$. Every pair inside one MSC simulation is distributed as a split-coupled pair.
2. (Pairwise variance.) For a parameterized family $X^\theta$ started at a common fixed state, and parameters with $\|\alpha_\varepsilon - \beta_\varepsilon\| \le C_0\varepsilon$, under the hypotheses of the split-coupling variance bound (with constants uniform in $\varepsilon$),

$$\mathbb{E}\Big[\sup_{t \le T}\big(f(X^{\alpha_\varepsilon}_{\mathrm{MSC}}(t)) - f(X^{\beta_\varepsilon}_{\mathrm{MSC}}(t))\big)^2\Big] \le C_T\,\varepsilon .$$

3. (Contrasts.) For $J \ge 2$ parameters within distance $C_0\varepsilon$ of each other and coefficients with $\sum_r c_r = 0$, the finite-difference numerator $N_\varepsilon(T) = \sum_{r=1}^J c_r f(X^{\theta_r^\varepsilon}_{\mathrm{MSC}}(T))$ satisfies $\mathbb{E}[N_\varepsilon(T)^2] = O(\varepsilon)$ and $\operatorname{Var} N_\varepsilon(T) = O(\varepsilon)$.

So a single MSC run gives all paths needed by central, higher-order or mixed-partial finite-difference schemes, while each pair keeps the $O(\varepsilon)$ variance of split coupling (independent sampling gives $O(1)$).

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](../gillespie-direct-method.md)

## Expansion

Project the MSC process onto coordinates $(i, j)$. Inside block $\ell$ both coordinates fire on a sub-interval of height $\lambda^{(i)}_\ell \wedge \lambda^{(j)}_\ell$, only one of them fires on sub-intervals of heights equal to the two excess intensities, and the rest of the block moves neither. These transition rates depend only on the projected state, so the projection is a Markov chain with exactly the split-coupling generator; uniqueness for nonexplosive chains gives equality in law. Part 2 then transfers the known split-coupling bound, and part 3 follows by writing $N_\varepsilon$ as a combination of pairwise differences (possible because $\sum_r c_r = 0$) and applying Cauchy–Schwarz.

## Sources

- D. F. Anderson and J. Ma, A general-purpose multi-path stacked coupling for stochastic reaction networks, arXiv (2026). <https://doi.org/10.48550/arXiv.2608.22627> (Theorem 2.2, Corollaries 4.1 and 4.2, Example 2.1.)
