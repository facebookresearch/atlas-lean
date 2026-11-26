# Persistence–exclusion dichotomy for three-species stochastic Kolmogorov systems

Consider three species following the stochastic Kolmogorov system

$$
dX_i=X_if_i(\mathbf X)\,dt+X_ig_i(\mathbf X)\,dE_i(t),\qquad i=1,2,3,
$$

with correlated Brownian environmental noise $\mathbf E=\Gamma^\top\mathbf B$, $\Gamma^\top\Gamma=\Sigma$. Assume the standing conditions: locally Lipschitz coefficients, non-degenerate noise, dissipativity at infinity, and $g_i^2$ growing slightly slower than $|f_i|$. For an ergodic invariant probability measure $\mu$ with species support $I_\mu\subseteq\{1,2,3\}$, the invasion rates are $\lambda_i(\mu)=\int(f_i-\tfrac{\sigma_{ii}}{2}g_i^2)\,d\mu$. Let $p_y(\mu)$ be the probability, starting from $y$, that the occupation measures $\frac1t\int_0^t\mathbf 1_{\{\mathbf X(s)\in\cdot\}}ds$ converge to $\mu$ and every species outside $I_\mu$ declines at an exponential rate. $\mathbf X$ is **strongly stochastically persistent** if there is a unique invariant probability measure $\mu$ with $I_\mu=\{1,2,3\}$ and $p_y(\mu)=1$ for all $y\in(0,\infty)^3$.

**Theorem.** Assume $\mathbf X$ is not a rock–paper–scissors system, and that all invasion rates are non-zero: $\lambda_i(\mu)\neq0$ for every ergodic $\mu$ and $i\notin I_\mu$.

*(1) Persistence.* $\mathbf X$ is strongly stochastically persistent iff

$$\max_{i}\lambda_i(\mu)>0\qquad\text{for every ergodic }\mu\text{ with }|I_\mu|\le2 .$$

In that case $\mathbb P_y(\mathbf X(t)\in\cdot)$ converges in total variation to the persistent invariant measure for every $y\in(0,\infty)^3$.

*(2) Exclusion.* Otherwise there are ergodic measures $\mu^1,\dots,\mu^k$ with $k\le3$ such that

- $|I_{\mu^i}|\le2$,
- no $I_{\mu^i}$ is contained in another $I_{\mu^j}$,
- $p_y(\mu^i)>0$ for every $i$ and every $y\in(0,\infty)^3$,
- $\sum_ip_y(\mu^i)=1$.

Every positive initial condition ends up, with positive probability, at each of these boundary communities, and the excluded species decay exponentially at rate $\lambda_i(\mu^\ell)<0$.

*(3) Genericity.* The non-zero invasion rate condition is generic: for any $\delta>0$, perturbing the $f_i$ by at most $\delta$ in sup norm, with $g$ unchanged, yields a system for which every ergodic measure has non-zero invasion rates.

Together with the rock–paper–scissors criterion and the one- and two-species classifications (exactly four outcomes for two species), the long-run behavior from positive initial conditions falls, up to relabeling species, into $10$ types. One type is extinction of all species; the other nine have at least one persisting species. Each type is determined by the signs of finitely many invasion rates.

## Depends on

- [Stochastic rock–paper–scissors persistence criterion](stochastic-rock-paper-scissors-persistence-criterion.md)

## Expansion

Non-degenerate noise means each face supports at most one ergodic measure, and those measures are fixed by the one- and two-species classifications. So the boundary dynamics reduce to finitely many communities, each with known invasion rates. Persistence follows from a general theorem for Kolmogorov SDEs: if every boundary invariant measure has some positive invasion rate (equivalently, some convex combination of invasion rates is positive), the system is strongly stochastically persistent. Non-degeneracy then gives a unique positive invariant measure and total-variation convergence. If some boundary community has only negative external invasion rates, a companion extinction theorem shows it captures trajectories with positive probability, and excluded species decay at the rate $\lambda_i<0$. Excluding rock–paper–scissors cycles (handled separately) rules out any other limit. Genericity is proved by induction on face dimension: subtracting small smooth bumps localized near each ergodic measure that has a zero invasion rate moves that rate off zero without disturbing lower-dimensional faces.

## Sources

- A. Hening, D. H. Nguyen, S. J. Schreiber, "A classification of the dynamics of three-dimensional stochastic ecological systems", arXiv preprint (2020), Section 3 (Propositions 3.2–3.3, Assumption 3.1, Theorems 3.2–3.4), Sections 4–5 (proofs, including Theorems 5.1–5.2) and Section 7 (classification), <https://doi.org/10.48550/arXiv.2004.00535>.
