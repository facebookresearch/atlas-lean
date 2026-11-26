# Existence of an optimal piecewise-constant Wolbachia release schedule under budget and production limits

**Model.** Dengue spreads between humans (susceptible $S_h$, infectious $I_h$, healthcare-seeking $J_h$, recovered $R_h$) and an *Aedes* population structured into aquatic, male and female (unmated, pregnant, infectious) compartments, each with a Wolbachia-carrying and a wild variant; Wolbachia-infected larvae are released at a time-dependent rate $r(t)$ into the aquatic compartment, and cytoplasmic incompatibility and reduced vector competence of Wolbachia carriers lower transmission. The right-hand side $F$ of this 18-dimensional ODE system is continuously differentiable, so for initial data in the biologically feasible region (aquatic population at most its carrying capacity $K_a$, adult classes bounded by the corresponding emergence-to-mortality ratios times $K_a$) the system has a unique local solution that stays in that region.

**Control problem.** Over a horizon of $T$ days, let the release be piecewise constant with $N$ periods of length $\ell=\lceil T/N\rceil$, $r(t)=\tilde r_i$ on period $i$, so that the controls are $\tilde r=(\tilde r_1,\dots,\tilde r_N)$. With unit release cost $C_r$, daily cost $C_J$ per healthcare-seeking case, budget $\tilde B$ and time-varying production capacity $P(t)$, minimize

$$\Phi(\tilde r)=\sum_{i=1}^N\ell\,C_r\,\tilde r_i+\sum_{t=1}^TC_J\,J_h(t;\tilde r)$$

over the admissible set

$$X=\Bigl\{\tilde r\in\mathbb R^N_{\ge0}:\ 0\le\tilde r_i\le P\bigl(\ell(i-1)+1\bigr),\ \ 0\le\sum_{i=1}^N\ell\,C_r\,\tilde r_i\le\tilde B\Bigr\}.$$

**Theorem.** The constrained problem has a minimizer in $X$.

A multi-objective version keeps release cost and hospitalization cost as separate objectives; its Pareto-optimal front is computed by the $\varepsilon$-constraint method (minimizing hospitalization cost subject to an upper bound on release cost and sweeping the bound).

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

$X$ is non-empty (it contains $\tilde r=0$), bounded (it lies in $[0,\max P]^N$) and closed (an intersection of closed half-spaces), hence compact. The release term of $\Phi$ is linear in $\tilde r$. The hospitalization term is continuous in $\tilde r$ because solutions of an ODE with a $C^1$ right-hand side depend continuously on parameters entering it continuously; the release enters the aquatic equation as a bounded forcing term, and on each period the solution map is continuous in the constant release level. Weierstrass' extreme value theorem then gives a minimizer. Numerically, earlier and higher release peaks reduce dengue prevalence more than the same total released later, which the optimizer exploits subject to production capacity.

## Sources

- Kyrho Corum, Renier Mendoza, Victoria May P. Mendoza, Arrianne Crystal Velasco, "Balancing Economic Cost and Disease Impact: Optimization Models for Wolbachia-Based Dengue Control", arXiv (2026). Section 2 (model), Section 3 (Theorem 3.1 existence and uniqueness, Theorem 3.2 forward invariance), Section 4 (single-objective problem and Theorem 4.1; multi-objective $\varepsilon$-constraint formulation). <https://doi.org/10.48550/arXiv.2601.10967>
