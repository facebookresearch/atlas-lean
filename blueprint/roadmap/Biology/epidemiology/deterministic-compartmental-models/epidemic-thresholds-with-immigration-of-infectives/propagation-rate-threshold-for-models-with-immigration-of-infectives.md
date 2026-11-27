# Propagation rate as an epidemic threshold for compartment models with immigration of infectives

**Setting.** Compartment models with susceptible-type variables $x \in \mathbb{R}^n$ and disease variables $y \in \mathbb{R}^m$ and an immigration flow $\Pi$ distributed over all compartments with proportions $p_1, \dots, p_{n+m}$:

$$x_i' = \Pi p_i + f_i(x, y), \qquad y_j' = \Pi p_{n+j} + g_j(x, y).$$

When infectious individuals immigrate ($p_{n+j} > 0$ for some $j$) there is no disease-free equilibrium, so $R_0$-type thresholds at a disease-free state no longer apply. Write $\mathbf{X}$ for the vector field and $\mathcal{S}$ for the disease-free hyperplane $\{y = 0\}$.

**Definition (propagation rate).** For a unit vector $\mathbf{u} = (0, \dots, 0, u_1, \dots, u_m)$ orthogonal to $\mathcal{S}$ with $u_j \ge 0$ (weights on disease stages), the propagation rate at a non-equilibrium state $\mathbf{p}$ is

$$X^{\mathbf{u}}(\mathbf{p}) = \frac{\langle\mathbf{X}(\mathbf{p}), \mathbf{u}\rangle}{\|\mathbf{X}(\mathbf{p})\|} = \frac{1}{\|\mathbf{X}(\mathbf{p})\|}\sum_{j=1}^m u_j\big(\Pi p_{n+j} + g_j(\mathbf{p})\big) \in [-1, 1].$$

The disease is spreading (in the weighted disease direction) when $X^{\mathbf{u}} > 0$ and declining when $X^{\mathbf{u}} < 0$; $X^{\mathbf{u}}(\mathbf{p}) = 0$ is an instantaneous epidemiological threshold, evaluable along trajectories $X^{\mathbf{u}}_{\mathbf{p}_0}(t) = X^{\mathbf{u}}(\varphi_{\mathbf{p}_0}(t))$.

**Theorem (asymptotic propagation rate).** Let $\mathbf{p}^*$ be a hyperbolic attracting (endemic) equilibrium whose eigenvalues satisfy $\mathrm{Re}\,\lambda_d \le \dots \le \mathrm{Re}\,\lambda_2 < \lambda_1 < 0$, with real leading eigenvalue $\lambda_1$ and unit leading eigenvector $\mathbf{v}_1 = (a_1, \dots, a_n, b_1, \dots, b_m)$, $b_m > 0$. Let $\mathcal{B}_\pm$ be the half-basins of $\mathbf{p}^*$ (excluding the trajectories that approach it along non-leading eigendirections) on which the last disease variable is eventually increasing, respectively decreasing. Then for $\mathbf{p}_0 \in \mathcal{B}_+$,

$$\lim_{t\to\infty}X^{\mathbf{u}}_{\mathbf{p}_0}(t) = u_1b_1 + \dots + u_mb_m,$$

and for $\mathbf{p}_0 \in \mathcal{B}_-$ the limit is $-(u_1b_1 + \dots + u_mb_m)$. Thus the long-run sign and size of the propagation rate are set by the disease components of the slowest eigendirection, independently of the initial condition within each half-basin.

## Proof sketch

Generic trajectories approach a hyperbolic sink tangent to the leading eigenvector, so the normalised velocity $\mathbf{X}/\|\mathbf{X}\|$ converges to $\pm\mathbf{v}_1$; projecting on $\mathbf{u}$ gives the limit, the sign being fixed by whether the approach is from the side where disease variables increase or decrease. The propagation rate is a scale-free, state-dependent replacement for $R_0$ that applies to open populations continually seeded by imported cases (e.g. arrival of infected travellers and vaccination-era reimportation), and it can be computed directly from the model's vector field.

## Sources

- Sofía Guarello, Nicolás González, Isabel Flores and Pablo Aguirre, "A geometric approach to the impact of immigration of people infected with communicable diseases", *Mathematical Biosciences* 378 (2024), 109320, <https://doi.org/10.1016/j.mbs.2024.109320>. Preprint version: arXiv:2308.01988 (2023), Section 2 (framework), Section 3 (propagation rate definitions and thresholds) and Section 6 (asymptotic lemma, half-basins and theorem), <https://doi.org/10.48550/arXiv.2308.01988>.
