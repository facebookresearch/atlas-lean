# Arrival-time estimate for metapopulation compartmental models via Kronecker splitting

**Setting.** Let a local $\ell$-compartment disease model have linearization $\mathrm{A}\in\mathbb{R}^{\ell\times\ell}$ at its disease-free equilibrium, and couple $N$ cities by a row-stochastic mobility matrix $\mathrm{P}$ with rate $\gamma$. The infected-class linearization of the network model is

$$
\dot{\mathbf{h}} = \tilde{\mathrm{A}}\mathbf{h} + \gamma(\tilde{\mathrm{P}} - \mathrm{I})\mathbf{h},\qquad \tilde{\mathrm{A}} = \mathrm{I}_N\otimes \mathrm{A},\quad \tilde{\mathrm{P}} = \mathrm{P}\otimes \mathrm{I}_\ell .
$$

**Splitting.** By the mixed-product rule, $\tilde{\mathrm{A}}\tilde{\mathrm{P}} = \mathrm{P}\otimes\mathrm{A} = \tilde{\mathrm{P}}\tilde{\mathrm{A}}$, so

$$
\mathbf{h}(t) = e^{(\tilde{\mathrm{A}} - \gamma\mathrm{I})t}\, e^{\gamma\tilde{\mathrm{P}}t}\,\mathbf{h}_0 ,
$$

separating local growth from network spread exactly.

**SEIR case.** For local SEIR dynamics (infection $\alpha$, incubation rate $\sigma$, recovery $\beta$), the exposed–infected block is $\mathrm{A} = \begin{pmatrix} -\sigma & \alpha\\ \sigma & -\beta\end{pmatrix}$ with $\det\mathrm{A} = -\sigma(\alpha-\beta)$, so the disease-free state is unstable exactly when $\alpha>\beta$, as for SIR. With dominant eigenvalue $\lambda_+$ and eigenvector ratios $\Gamma_\pm = \big(\beta-\sigma\pm\sqrt{(\beta-\sigma)^2+4\sigma\alpha}\big)/(2\sigma)$, seeding a fraction $\chi_0$ of infecteds in city $n$ and keeping the leading terms in $\gamma$ and in $e^{\lambda_+ t}$ gives the arrival time at threshold $\kappa$ in city $m$:

$$
\tau_{mn} = \frac{d_m}{\lambda_+}\, W\!\left(\frac{1}{\gamma}\frac{\lambda_+}{d_m}\Big(\frac{\kappa\, d_m!\,(\Gamma_- - \Gamma_+)}{\chi_0\,\rho_m\,\Gamma_-}\Big)^{1/d_m}\right) + o(1),
$$

where $d_m$ is the graph distance and $\rho_m = \boldsymbol{\delta}_m^{\mathsf T}\mathrm{P}^{d_m}\boldsymbol{\delta}_n$. As $\sigma\to\infty$, $\Gamma_\pm\to -\tfrac12\pm\tfrac12$ and the formula reduces to the SIR estimate with $\lambda_+$ replaced by $\alpha-\beta$.

**General compartments.** If $\mathrm{A} = \mathrm{Q}\mathrm{D}\mathrm{Q}^{-1}$ is diagonalizable with leading eigenvalue $\lambda_1$, and $\Xi(\mathrm{A}) = \tilde{\boldsymbol{\delta}}_1^{\mathsf T}\mathrm{Q}\,\mathrm{diag}(\lambda_1,0,\dots,0)\,\mathrm{Q}^{-1}\tilde{\boldsymbol{\delta}}_1$ is the paper's projection constant (infected compartment listed first), the analogous estimate is

$$
\tau_{mn} = \frac{d_m}{\lambda_1}\, W\!\left(\frac{1}{\gamma}\frac{\lambda_1}{d_m}\Big(\frac{\kappa\, d_m!\,\Xi(\mathrm{A})}{\chi_0\rho_m}\Big)^{1/d_m}\right) + o(1).
$$

## Proof sketch

Expand $e^{\gamma\tilde{\mathrm{P}}t} = \sum_k \gamma^k t^k (\mathrm{P}^k\otimes\mathrm{I}_\ell)/k!$; the $(m,n)$ block vanishes for $k<d_m$, so the first nonzero term is $\gamma^{d_m}t^{d_m}\rho_m/d_m!$. The local factor is $\tilde{\boldsymbol{\delta}}^{\mathsf T}\mathrm{Q}e^{\mathrm{D}t}\mathrm{Q}^{-1}\tilde{\boldsymbol{\delta}}$, dominated by $e^{\lambda_+ t}$. Setting the product equal to $\kappa$ gives an equation of the form $c\,\tau^{d}e^{\lambda\tau} = \kappa$, solved by the Lambert $W$ function. These are formal leading-order estimates in the small-mobility limit, checked numerically on a global airline network.

## Depends on

- [Linearized arrival times bound metapopulation SIR arrival times from below](linearized-arrival-times-bound-metapopulation-sir-arrival-times.md)

## Sources

- Ashley Armbruster, Matt Holzer, Noah Roselli and Lena Underwood, "Epidemic Spreading on Complex Networks as Front Propagation into an Unstable State", *Bulletin of Mathematical Biology* 85 (2023), 4, <https://doi.org/10.1007/s11538-022-01110-7>. Preprint version: arXiv:2109.11985 (2021), Section 3, the SEIR arrival-time estimate and the remark on general compartmental models, <https://doi.org/10.48550/arXiv.2109.11985>.
