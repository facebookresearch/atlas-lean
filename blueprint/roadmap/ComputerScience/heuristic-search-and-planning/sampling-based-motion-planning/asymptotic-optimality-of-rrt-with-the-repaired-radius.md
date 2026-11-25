# Asymptotic optimality of RRT* with the repaired radius (Solovey et al.)

Let $(F, s, t)$ be a robustly feasible motion-planning problem in a $d$-dimensional Euclidean configuration space with free
space $F$ of finite positive measure $\lvert F \rvert$, samples drawn independently and uniformly from $F$, and robust optimum $c^*$ (the
infimum of the cost over paths $\sigma$ from $s$ to $t$ with $B_\delta(\sigma) \subseteq F$ for some $\delta > 0$), and fix a steering size $\eta > 0$, $\varepsilon \in (0, 1)$,
$\theta \in (0, 1/4)$ and $\mu \in (0, 1)$. If RRT\* connects and rewires within distance $\min\{r(\lvert V \rvert), \eta\}$ of each new vertex, $V$ the current vertex set, with
$r(n) = \gamma (\log n/n)^{1/(d+1)}$ and
$\gamma \ge (2 + \theta)\bigl((1 + \varepsilon/4) c^* \lvert F \rvert / ((d+1)\theta(1 - \mu)\zeta_d)\bigr)^{1/(d+1)}$, $\zeta_d$ the volume of the
unit $d$-ball, then, with $\sigma_n$ the path returned after $n$ iterations, $\lim_{n \to \infty} \Pr[c(\sigma_n) \le (1 + \varepsilon)c^*] = 1$ (Solovey, Janson, Schmerling, Frazzoli and Pavone,
Theorem 1 and equation (3)). This is convergence in probability to within a factor $1 + \varepsilon$ for every fixed $\varepsilon$, not
almost-sure convergence; the exponent $1/(d+1)$ accounts for the order in which samples arrive.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Robust feasibility, probabilistic completeness and asymptotic optimality.
- Statement prerequisite: PRM, PRM*, RRT and RRT* as abstract algorithms over sample sequences.

## Sources

- Revisiting the Asymptotic Optimality of RRT* — K. Solovey, L. Janson, E. Schmerling, E. Frazzoli, M. Pavone, ICRA 2020, Sec. II (Definitions 2 and 3, Algorithm 2); Sec. IV, Theorem 1 and equations (2)–(3); Abstract (exponent $1/d$ replaced by $1/(d+1)$). <https://par.nsf.gov/servlets/purl/10192531>
