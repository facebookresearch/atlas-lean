# Posterior mean genetic liability given case-control status and family history

**Model.** In the liability threshold model each individual has a standard normal liability $\epsilon = \epsilon_g + \epsilon_e$ with genetic part $\epsilon_g \sim N(0, h^2)$ and independent environmental part $\epsilon_e \sim N(0, 1 - h^2)$, where $h^2 \in (0,1)$ is the narrow-sense heritability of liability. An individual is a case ($z = 1$) iff $\epsilon \ge T$, so the prevalence is $K = P(\epsilon \ge T) = 1 - \Phi(T)$. Liabilities of relatives are jointly normal with $\mathrm{Cov}(\epsilon_1, \epsilon_2) = K_{12} h^2$, where $K_{12}$ is the coefficient of relationship ($1/2$ for parent–offspring and full siblings, $0$ for the two parents). For a genotyped offspring $o$ with parents $p_1, p_2$ and a sibling $s$,

$$\begin{pmatrix} \epsilon_{o,e} \\ \epsilon_{o,g} \\ \epsilon_{p_1} \\ \epsilon_{p_2} \\ \epsilon_s \end{pmatrix} \sim \mathrm{MVN}_5\!\left( 0,\ \begin{pmatrix} 1-h^2 & 0 & 0 & 0 & 0 \\ 0 & h^2 & \tfrac12 h^2 & \tfrac12 h^2 & \tfrac12 h^2 \\ 0 & \tfrac12 h^2 & 1 & 0 & \tfrac12 h^2 \\ 0 & \tfrac12 h^2 & 0 & 1 & \tfrac12 h^2 \\ 0 & \tfrac12 h^2 & \tfrac12 h^2 & \tfrac12 h^2 & 1 \end{pmatrix} \right).$$

**Target.** The posterior mean genetic liability is

$$\hat\epsilon_{o,g} = E\big[\epsilon_{o,g} \mid z_o, z_{p_1}, z_{p_2}, z_s\big],$$

conditioning only on the statuses that are observed. It depends on the data only through the configuration of statuses, so it is computed once per configuration (for example by Monte Carlo integration of the truncated multivariate normal) and looked up per individual. Several siblings enter through events such as "at least one sibling affected", i.e. $\max_i \epsilon_{s_i} \ge T$.

**Closed form without family history.** If only $z_o$ is observed,

$$E[\epsilon_{o,g} \mid z_o = 1] = \frac{h^2 \varphi(T)}{K}, \qquad E[\epsilon_{o,g} \mid z_o = 0] = -\frac{h^2 \varphi(T)}{1-K},$$

with $\varphi$ the standard normal density; in particular $\hat\epsilon_{o,g}$ is then an affine function of $z_o$.

Example (Hujoel et al.): with $K = 5\%$, $h^2 = 50\%$ and parental history only, the posterior mean is $-0.10$ for a control with no affected parent, $0.39$ for a control with one affected parent and $1.56$ for a case with two affected parents; case-control GWAS treats the first two identically.

## Depends on

- [Case indicator of the threshold model](../../../liability-scale-heritability-from-ld-score-regre/case-ind.md)

## Expansion

Since $(\epsilon_{o,g}, \epsilon_o)$ is bivariate normal with $\mathrm{Cov}(\epsilon_{o,g}, \epsilon_o) = h^2$ and $\mathrm{Var}(\epsilon_o) = 1$, $E[\epsilon_{o,g} \mid \epsilon_o] = h^2 \epsilon_o$, and the mean of a standard normal truncated to $[T, \infty)$ is $\varphi(T)/K$ (to $(-\infty, T)$ it is $-\varphi(T)/(1-K)$); the tower property gives the closed form. With relatives, conditioning on several threshold events has no simple closed form; the Pearson–Aitken selection formula gives an analytical approximation, while Monte Carlo sampling from the multivariate normal (with conditional resampling in the tails until each configuration's standard error is below $0.01$) handles arbitrary configurations, including the "at least one sibling" event. Using the posterior mean of the genetic component rather than of the total liability integrates out environmental noise and raises association power.

## Sources

- M. L. A. Hujoel, S. Gazal, P.-R. Loh, N. Patterson and A. L. Price, "Liability threshold modeling of case-control status and family history of disease increases association power", Nature Genetics 52 (2020), 541–547, Results ("Overview of methods") and Methods (Equation 1), <https://doi.org/10.1038/s41588-020-0613-6>, PMCID: PMC7210076.
