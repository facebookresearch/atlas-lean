# Mean and variance of mRNA and protein numbers with general lifetimes

**Model.** A gene switches between active and inactive states as a two-state Markov process $Y(t) \in \{0, 1\}$, with activation rate $\lambda_1^+$ and inactivation rate $\lambda_1^-$; write $\Lambda = \lambda_1^+ + \lambda_1^-$ and $\delta_+ = \lambda_1^+/\Lambda$ for the stationary probability of being active. While the gene is active, mRNAs are created at the instants of a Poisson process of rate $\lambda_2$; each mRNA lives an independent time with **arbitrary** distribution $F_2$ (mean $\mathbb{E}\sigma_2$) and, while alive, produces proteins at the instants of a Poisson process of rate $\lambda_3$; each protein lives an independent time with arbitrary distribution $F_3$ (mean $\mathbb{E}\sigma_3$). Set $\rho_2 = \lambda_2 \mathbb{E}\sigma_2$, $\rho_3 = \lambda_3\mathbb{E}\sigma_3$, and let $\overline F_j(x) = (1 - F_j([0,x]))/\mathbb{E}\sigma_j$ be the normalized tail, the density of the equilibrium residual lifetime.

**Representation.** At equilibrium, with $\mathcal{N}_{\lambda_2}$ a marked Poisson process of intensity $\lambda_2\,\mathrm{d}u \otimes F_2(\mathrm{d}v)$ (creation time $u$, lifetime $v$) independent of the stationary process $Y$, the number of mRNAs present at time $0$ is

$$
M = \int_{\mathbb{R}\times\mathbb{R}_+} \mathbf{1}\{u \le 0 \le u + v,\ Y(u) = 1\}\,\mathcal{N}_{\lambda_2}(\mathrm{d}u, \mathrm{d}v),
$$

and the number of proteins $P$ has the analogous two-level representation, with an independent marked Poisson process of protein creations attached to each mRNA during its lifetime.

**Theorem (mRNA).**

$$
\mathbb{E}(M) = \delta_+\rho_2, \qquad \operatorname{Var}(M) = \mathbb{E}(M) + 2\rho_2^2\,\delta_+(1 - \delta_+)\int_0^\infty\!\!\int_0^\infty e^{-\Lambda v}\,\overline F_2(u)\,\overline F_2(u + v)\,\mathrm{d}u\,\mathrm{d}v .
$$

**Theorem (protein).** $\mathbb{E}(P) = \delta_+\rho_2\rho_3$ and

$$
\begin{aligned}
\operatorname{Var}(P) = \mathbb{E}(P) &+ \lambda_2\rho_3^2\,\delta_+\int_0^\infty\!\!\int_{\mathbb{R}_+}\Big[\int_{-s}^{(t - s)\wedge 0}\overline F_3(-u)\,\mathrm{d}u\Big]^2\,\mathrm{d}s\,F_2(\mathrm{d}t)\\
&+ \rho_2^2\rho_3^2\,\delta_+(1 - \delta_+)\int_{\mathbb{R}_+^4} e^{-\Lambda|(u_1 - u_2) + (v_1 - v_2)|}\prod_{i=1}^2 \overline F_2(u_i)\,\overline F_3(v_i)\,\mathrm{d}u_i\,\mathrm{d}v_i .
\end{aligned}
$$

The source's (9) prints $\overline F_3(u)$ in the inner integral of the first excess term, which makes that term infinite; $\overline F_3(-u)$ follows from the conditional mean displayed before its Theorem 2. The first excess term is the noise from random mRNA lifetimes and translation bursts; the second is the noise from gene switching, which vanishes when $\delta_+ \in \{0, 1\}$.

## Expansion

The marked Poisson process $\mathcal{M} = \int \mathbf{1}\{Y(u) = 1\}\,\delta_{(u,v)}\,\mathcal{N}_{\lambda_2}(\mathrm{d}u, \mathrm{d}v)$ of mRNA creation times and lifetimes is a Poisson process thinned by the independent gene state. Conditionally on $Y$, $M$ is Poisson with mean $\lambda_2\int \mathbf{1}\{Y(u) = 1\}(1 - F_2(-u))\,\mathrm{d}u$, so the law of total variance gives the Poisson term $\mathbb{E}(M)$ plus the variance of this conditional mean. That variance is computed from the stationary covariance of the telegraph process, $\operatorname{Cov}(Y(u), Y(w)) = \delta_+(1 - \delta_+)e^{-\Lambda|u - w|}$. For proteins the same conditioning is applied twice, first on $Y$ and then on the mRNA process, with Laplace functionals of marked Poisson processes. With exponential lifetimes the formulas recover the classical Markovian results obtained from Fokker-Planck equations. Comparing exponential with deterministic or Gaussian lifetimes of the same mean shows that the shape of the lifetime distribution, not only its mean, changes the protein variance.

## Sources

- Vincent Fromion, Emanuele Leoncini and Philippe Robert, "Stochastic Gene Expression in Cells: A Point Process Approach", arXiv (2012), Section 2 (model), Proposition 1 and Theorem 1 (mRNA point process), Proposition 2 (mRNA mean and variance), Proposition 3 and Theorem 2 (protein mean and variance), appendix Proposition 4 (Laplace functional of marked Poisson processes), <https://doi.org/10.48550/arXiv.1206.0362>.
