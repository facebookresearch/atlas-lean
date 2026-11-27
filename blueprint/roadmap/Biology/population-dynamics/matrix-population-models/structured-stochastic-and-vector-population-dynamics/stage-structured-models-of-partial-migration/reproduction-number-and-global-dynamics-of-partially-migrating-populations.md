# Reproduction number and global dynamics of partially migrating populations

**Linear models.** Let $A^s_n$ and $A^r_m$ be the Leslie-type projection matrices of an isolated $n$-stage migrant population and an isolated $m$-stage resident population (fecundities $f_i$ in the first row, survival probabilities $t_i$ on the subdiagonal), with basic reproduction numbers $R^s_0$ and $R^r_0$, where $R_0 = \rho(F(I - T)^{-1})$ for the fecundity part $F$ and transition part $T$.

- With a **single egg pool**, a fraction $\phi \in (0,1)$ of all eggs becomes migrants and the coupled reproduction number is $R^{c1}_0(\phi) = \phi R^s_0 + (1 - \phi)R^r_0$, the expected number of eggs produced by one egg.
- With **two egg pools**, migrants put a fraction $\phi_s$ of their eggs into the migrant pool and residents a fraction $\phi_r$ into the resident pool. The coupled reproduction number is

$$R^{c2}_0(\phi_s,\phi_r) = \rho\begin{pmatrix}\phi_s R^s_0 & (1 - \phi_r)R^r_0\\ (1 - \phi_s)R^s_0 & \phi_r R^r_0\end{pmatrix} = \frac{\phi_s R^s_0 + \phi_r R^r_0 + \sqrt{(\phi_s R^s_0 + \phi_r R^r_0)^2 - 4R^s_0 R^r_0(\phi_s + \phi_r - 1)}}{2}.$$

**Proposition.** If $R^s_0 = R^r_0$, then $R^{c2}_0 \equiv R^s_0$ on $D = [0,1]^2$. If $R^s_0 \ne R^r_0$, $R^{c2}_0$ has no interior extrema on $D$; for $R^r_0 < R^s_0$ its maximum $R^s_0$ is attained on the edge $\phi_s = 1$, and for $R^s_0 < R^r_0$ its maximum $R^r_0$ on the edge $\phi_r = 1$. Thus mixing life histories never raises the reproduction number above that of the better pure strategy.

**Nonlinear models.** Replace the survival probabilities by density-dependent $t_i(x)$, with stage map $x_{i+1}(t+1) = s_i(x_i(t)) := x_i(t)\,t_i(x_i(t))$ and $x_1(t+1) = \sum_j f_j x_j(t)$, and assume (A1) $t_i \in C^1$, $0 < t_i \le 1$, strictly decreasing; (A2) $s_i$ strictly increasing and bounded; (A3) $f_j \ge 0$, $f_n > 0$ (Beverton–Holt $t_i(x) = b_i/(1 + c_i x)$ is an example).

**Theorem.** If every $s_i$ is strongly sublinear on $\mathbb{R}_+$ ($\lambda s_i(x) < s_i(\lambda x)$ for $0 < \lambda < 1$, $x > 0$), then for the isolated model, for the single-egg-pool coupled model and for the two-egg-pool coupled model, with $R_0$ the reproduction number of the linearization at the origin ($R^{c1}_0$, $R^{c2}_0$ respectively): if $R_0 < 1$ the origin is the only fixed point and is globally asymptotically stable; if $R_0 > 1$ there is a unique positive fixed point, which is locally stable and attracts every nonzero orbit.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The two-pool matrix $\begin{pmatrix}\phi_s R^s_0 & (1-\phi_r)R^r_0\\ (1-\phi_s)R^s_0 & \phi_r R^r_0\end{pmatrix}$ is the next-generation matrix between egg pools; its spectral radius is the larger root of its characteristic polynomial. Computing the gradient shows it vanishes only where $R^s_0 = R^r_0$, so extrema lie on the boundary, where direct evaluation gives the stated maxima. The nonlinear result follows from the cone limit-set trichotomy for monotone maps: if a continuous monotone map $F$ on $\mathbb{R}^n_+$ has an iterate $F^r$ that is strongly sublinear, strongly positive on nonzero points and order compact, then either all orbits are unbounded, or all converge to $0$, or there is a unique positive fixed point attracting all nonzero orbits. Bounded $s_i$ rules out unboundedness and the sign of $R_0 - 1$ (stability of the origin) selects between the other two alternatives.

## Sources

- Anushaya Mohapatra, Haley A. Ohms, David A. Lytle, Patrick De Leenheer, "Population models with partial migration", Journal of Difference Equations and Applications 22 (2016), 316–329, <https://doi.org/10.1080/10236198.2015.1091451>. Published version of arXiv:1510.00840, cited next; locators there refer to the arXiv version.
- Anushaya Mohapatra, Haley A. Ohms, David A. Lytle, Patrick De Leenheer, "Population models with partial migration", arXiv (2015). Section 2 (coupled linear models, $R^{c1}_0$, $R^{c2}_0$), Proposition 2.1, Definitions 3.1–3.4, Theorem 3.5, Theorem 3.6, Theorem 3.7, Theorem 3.8. <https://doi.org/10.48550/arXiv.1510.00840>
