# Ancestral mean estimation in branching processes in random environments

**Model.** For replicates $j=1,\dots,J$, let $Z_{n+1,j}=\sum_{k=1}^{Z_{n,j}}\xi_{n,j,k}$ be a branching process in i.i.d. random environments $\zeta_{n,j}$: given $\zeta_{n,j}$ the offspring counts $\xi_{n,j,k}$ are i.i.d. with law $p(\cdot\mid\zeta_{n,j})$, conditional mean $m_{n,j}$ and variance $\sigma^2_{n,j}$. Assume $p(0\mid\zeta)=0$ (supercritical, no extinction), $\mathbb P(p(1\mid\zeta)<1)=1$, and write $m^*=\mathbb E m_{0,1}$, $m_2^*=\mathbb E m_{0,1}^2$, $\sigma^{2*}=\operatorname{Var}m_{0,1}$, $\gamma^{2*}=\mathbb E\sigma^2_{0,1}<\infty$, and $r^{*2}=m_2^*/m^{*2}\ge1$ (the environmental coefficient of variation, $r^*>1$ unless the environment is degenerate). The ancestor $Z_{0,j}$ is unobserved, with mean $m_A$ and variance $\sigma_A^2$; generations $\tau_n,\dots,n$ are observed. This models PCR amplification (molecules, cycles with random efficiency) and early epidemic growth (cases, weeks).

**Estimators.** With
$$\hat m_n=\frac1{J}\sum_{j}\frac1{n-\tau_n}\sum_{l=\tau_n+1}^n\frac{Z_{l,j}}{Z_{l-1,j}},\qquad \hat m_{A,n}=\frac{1}{\hat{\mathcal N}_n}\cdot\frac1J\sum_j\sum_{l=\tau_n}^nZ_{l,j},$$
where $\hat{\mathcal N}_n$ plugs $\hat m_n$ into $\mathcal N_n^*=m^{*\tau_n}(m^{*(n-\tau_n+1)}-1)/(m^*-1)$ (because $\mathbb E Z_{l,j}=m_Am^{*l}$), and $\hat r_n=\sqrt{\hat m_{2,n}}/\hat m_n$ with $\hat m_{2,n}$ the analogous mean of squared ratios.

**Theorem.** Suppose $n/\log J_n\to0$ and either $\tau_n$ is fixed, $n-\tau_n=\delta$ is fixed, or both $\tau_n,n-\tau_n\to\infty$. Then $\hat m_{A,n}\to m_A$ in probability, and if $m^*_{4+2\delta'}<\infty$ and $\mathbb E Z_{0,1}^{4+2\delta'}<\infty$ for some $\delta'>0$,
$$\frac{\sqrt{J_n}}{\hat r_n^{\,n}}\big(\hat m_{A,n}-m_A\big)\ \xrightarrow{d}\ N(0,\sigma_\tau^2),$$
with an explicit finite positive $\sigma^2_\tau$ depending on the sampling regime and on $\mathfrak D=\frac{m_A\gamma^{2*}}{1-(r^{*2}m^*)^{-1}}+\frac{(m_A^2+\sigma_A^2)\sigma^{2*}}{1-r^{*-2}}$. Meanwhile $\sqrt{J_n(n-\tau_n)}(\hat m_n-m^*)\to N(0,\sigma^{2*})$ when $J_n(n-\tau_n)\to\infty$, and when $m^*$ and $m_A$ are learned from disjoint generation blocks the two estimators are asymptotically independent Gaussians; learning $m^*$ from the later block gives a smaller asymptotic variance for $\hat m_{A,n}$.

## Expansion

In a Galton-Watson process the ancestor mean is estimated at rate $\sqrt J$ through the martingale limit of $Z_n/m^n$. In a random environment $Z_n/m^{*n}$ is not a martingale in the marginal sense and its variance grows like $r^{*2n}$, because the product of random environmental means fluctuates; so the effective number of replicates is $J/r^{*2n}$, which is why the scaling carries $\hat r_n^{\,n}$ and why the number of generations must be small relative to $\log J$. A key lemma is that $(\hat m_n/m^*)^n\to1$ in probability when $n^2/(J_n(n-\tau_n))\to0$, controlling the plug-in error in $\hat{\mathcal N}_n$; bounds $\mathbb E[1/Z_n]\le c a^n$ ($a<1$) handle the ratio estimator. The theory is applied to relative quantitation in real-time PCR and to the number of initial COVID-19 cases across groups of counties.

## Sources

- X. Jiang, A. N. Vidyashankar, "Ancestral inference and learning for branching processes in random environments", arXiv:2501.16526 (2025), Sections 1.3 and 2 (Sampling Scheme 1.1, Theorems 2.1-2.3, Lemma 2.4), Section 3 (Theorems 3.1-3.3), Section 4 (Lemma 4.1, Theorem 4.3), <https://doi.org/10.48550/arXiv.2501.16526>.
