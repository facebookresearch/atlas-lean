# Positive solutions near segregated profiles under strong competition

**Setting.** As for segregated profiles of Lotka-Volterra competition-diffusion systems: $k \ge 2$ species, $\alpha_{ij} > 0$ for $i \ne j$ (not necessarily symmetric), and
$$-u_i'' - c u_i' = \mu u_i(1 - u_i) - \beta u_i \sum_{j \ne i} \alpha_{ij} u_j \ \text{ in } (-\pi,\pi), \qquad u_i(\pm\pi) = 0. \tag{P}$$
Write $\varepsilon = \beta^{-1/3}$.

**Theorem 1.2 (one interval per species).** Let $\mu > (c^2 + k^2)/4$ and let $\mathbf U$ be the segregated profile in which species $1, \dots, k$ occupy consecutive intervals with interfaces $s_1 < \dots < s_{k-1}$. There are $\beta_0, C_1, C_2 > 0$ such that for every $\beta \ge \beta_0$, (P) has a solution $\mathbf u_\beta$ with all components strictly positive in $(-\pi,\pi)$ and
$$C_1 \beta^{-1/3} \le \|\mathbf u_\beta - \mathbf U\|_\infty \le C_2 \beta^{-1/3}.$$
Near each interface, with $h = r - s_i$ and $z = h/\varepsilon$, uniformly for $|h| \le M'\varepsilon \log\beta$,
$$u_{\beta,i}(r) = \varepsilon a_1^{(i)}(z) + O(\varepsilon^2 + h^2), \qquad u_{\beta,i+1}(r) = \varepsilon a_2^{(i)}(z) + O(\varepsilon^2 + h^2),$$
where $\mathbf a^{(i)}$ is the two-species interface profile with coefficients $(\alpha_{i,i+1}, \alpha_{i+1,i})$ and the profile slopes at $s_i$; all other components are at most $C e^{-1/(C\varepsilon)}$ there. In particular $\varepsilon^{-1}(u_{\beta,i}, u_{\beta,i+1})(s_i + \varepsilon z) \to \mathbf a^{(i)}(z)$ in $C^2_{\mathrm{loc}}(\mathbb{R})$. The hypothesis $\mu > (c^2+k^2)/4$ is optimal, since below it no such profile exists.

**Theorem 1.4 (repeated labels and multiplicity).** For $m \ge k$, $\mu > (c^2 + m^2)/4$ and any labelling $\sigma$ of $m$ intervals (consecutive intervals carry different species, every species occurs), the same conclusions hold near the corresponding profile. Since distinct labellings give distinct limits, if $m_0$ is the largest integer strictly less than $2\sqrt{\mu - c^2/4}$, then for all sufficiently large $\beta$ system (P) has at least
$$\sum_{m=k}^{m_0} \sum_{i=0}^{k} (-1)^i \binom{k}{i} (k-i)(k-i-1)^{m-1}$$
distinct positive solutions. The inner sum counts the surjective labellings of $m$ intervals by $k$ species with no two neighbours equal (inclusion-exclusion over omitted species).

**Theorem 1.6 (radial problem).** On the ball $B_R \subset \mathbb{R}^n$, $n \ge 2$, with Dirichlet data at $r = R$, if $\mu > j_{(n-2)/2,m}^2/R^2$ the same construction gives, for each labelling of $m$ shells, a radial positive solution within $O(\beta^{-1/3})$ of the radial profile, with the same interface asymptotics; with $M_\mu = \#\{m \ge 1 : j_{(n-2)/2,m} < R\sqrt{\mu}\}$ the number of distinct positive radial solutions is at least $\sum_{m=k}^{M_\mu} \sum_{i=0}^k (-1)^i \binom{k}{i} (k-i)(k-i-1)^{m-1}$.

**Proposition 1.7 (obstruction from a vanishing coefficient).** Let $j \ne l$ with $\alpha_{jl} = 0$, $\alpha_{hl} > 0$ for every $h \notin \{j, l\}$, and all other coefficients nonnegative. Then no sequence of positive solutions with $\beta \to \infty$ converges uniformly to a segregated profile (on the interval or the ball) satisfying the corresponding endpoint and flux conditions.

## Expansion

The proof is a constructive perturbation argument. At each interface both limiting densities vanish linearly, and balancing diffusion against competition gives the inner scale $\varepsilon = \beta^{-1/3}$ in both space and amplitude; the two-species interface profile, corrected at order $\varepsilon$, is matched to the Taylor expansions of the logistic solutions on either side to build an approximate solution with small residual. The linearized operator is inverted with bounds uniform in $\beta$ by taking at each interface the weighted difference of the two equations, in which the mutual competition terms cancel; in the limit these differences solve the linearized profile problem, which has only the trivial solution because the segregated profile is nondegenerate. Scalar barrier estimates then control each component, a contraction mapping corrects the approximate solution, and a maximum principle shows the corrected solution is positive. For the obstruction, on a subinterval $D$ of the region occupied by $l$ with $\lambda_1(D) < \mu$, uniform convergence keeps $u_l \ge c_0 > 0$, so competition with $l$ makes every third species $h$ exponentially small in $\sqrt\beta$ and $\beta u_h \to 0$ there. Since $\alpha_{jl} = 0$, testing the equation of $u_j$ against the first Dirichlet eigenfunction of $D$ gives $\int_D [\mu - \lambda_1(D) - \mu u_j - \beta\sum_{h \notin\{j,l\}} \alpha_{jh} u_h]\, u_j \varphi \le 0$ (with the appropriate radial or drift weight). If $u_j \to 0$ uniformly on $D$, as the profile requires, the bracket tends to $\mu - \lambda_1(D) > 0$ while $u_j > 0$, a contradiction.

## Depends on

- [Segregated profiles of Lotka-Volterra competition-diffusion systems](segregated-profiles-of-lotka-volterra-competition-diffusion-systems.md)

## Sources

- Z. Li, S. Terracini, "Multiple positive solutions near segregated profiles in Lotka-Volterra competition systems with asymmetric interactions" (2026), Theorems 1.2, 1.4 and 1.6, Proposition 1.7, with the construction in Sections 2-5, <https://doi.org/10.48550/arXiv.2611.33975>.
