# Hadamard-product covariance of a marker-by-environment interaction

Let $x_{jm}$ be the genotype of line $j$ at marker $m$ ($m = 1,\dots,p$), and let $W_{ijq}$ be the value of environmental covariate $q$ ($q = 1,\dots,Q$) for line $j$ in environment $i$, both treated as fixed. Define a random genetic score and a random environmental score

$$\tilde g_j = \sum_{m=1}^{p} x_{jm}\tilde b_m, \qquad \tilde w_{ij} = \sum_{q=1}^{Q} W_{ijq}\tilde\gamma_q ,$$

where the $\tilde b_m$ are i.i.d. with mean $0$ and variance $\sigma_b^2$, the $\tilde\gamma_q$ are i.i.d. with mean $0$ and variance $\sigma_\gamma^2$, and the two families are independent. Then the multiplicative interaction $gw_{ij} = \tilde g_j \tilde w_{ij}$ has mean $0$ and covariance

$$\operatorname{Cov}(gw_{ij}, gw_{i'j'}) = \operatorname{Cov}(\tilde g_j, \tilde g_{j'})\,\operatorname{Cov}(\tilde w_{ij}, \tilde w_{i'j'}) \propto G_{jj'}\,\Omega_{ij,i'j'},$$

where $G$ is the marker-based genomic relationship matrix and $\Omega$ is the analogous similarity matrix built from the environmental covariates. For a vector of records with genetic incidence matrix $Z_g$, the interaction vector therefore has covariance $\bigl[Z_g G Z_g^{\top}\bigr]\circ\Omega\,\sigma_{gw}^2$, a Hadamard (entrywise) product. This gives the reaction-norm model

$$y_{ijk} = \mu + w_{ij} + g_j + gw_{ij} + \varepsilon_{ijk}, \quad \mathbf w \sim N(0, \Omega\sigma_w^2), \quad \mathbf g \sim N(0, G\sigma_g^2), \quad \mathbf{gw} \sim N\bigl(0, [Z_gGZ_g^{\top}]\circ\Omega\,\sigma_{gw}^2\bigr),$$

with i.i.d. $N(0,\sigma_\varepsilon^2)$ errors. Replacing $\Omega$ by $Z_E Z_E^{\top}$, the incidence kernel of environments, gives the marker-by-environment term $\mathbf{gE} \sim N\bigl(0, [Z_gGZ_g^{\top}]\circ[Z_EZ_E^{\top}]\,\sigma_{gE}^2\bigr)$.

## Proof sketch

Since both scores have mean zero and are independent, $\mathbb{E}[\tilde g_j\tilde w_{ij}] = 0$ and $\mathbb{E}[\tilde g_j\tilde w_{ij}\tilde g_{j'}\tilde w_{i'j'}] = \mathbb{E}[\tilde g_j\tilde g_{j'}]\,\mathbb{E}[\tilde w_{ij}\tilde w_{i'j'}]$. Each factor is a quadratic form in the fixed covariates: $\sigma_b^2\sum_m x_{jm}x_{j'm}$ and $\sigma_\gamma^2\sum_q W_{ijq}W_{i'j'q}$. After centering and scaling these are proportional to $G_{jj'}$ and $\Omega_{ij,i'j'}$. By the Schur product theorem the Hadamard product of two positive semidefinite kernels is positive semidefinite, so the interaction kernel is a valid covariance. Two records are correlated through the interaction only when they are similar both genetically and environmentally. The model needs only the two kernels, not $pQ$ explicit marker-by-covariate contrasts. The same algebra gives the Cockerham–Kempthorne epistatic covariances between relatives.

## Depends on

- [Genetic relationship matrix entry](../../../genomic-relationship-matrices/grm.md)

## Sources

- D. Jarquín, J. Crossa, X. Lacaze, P. Du Cheyron, J. Daucourt, J. Lorgeou, F. Piraux, L. Guerreiro, P. Pérez, M. Calus, J. Burgueño, G. de los Campos, *A reaction norm model for genomic selection using high-dimensional genomic and environmental data*, Theoretical and Applied Genetics 127 (2014), 595–607, <https://doi.org/10.1007/s00122-013-2243-1>, PMCID PMC3931944. Models Eqs. (1)–(6); covariance derivation in "Incorporating interactions between markers and environmental covariates".
