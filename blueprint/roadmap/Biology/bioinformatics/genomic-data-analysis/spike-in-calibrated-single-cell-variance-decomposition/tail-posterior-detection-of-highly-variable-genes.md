# Tail-posterior detection of highly variable genes

**Setting.** In the [hierarchical Poisson–gamma model with spike-ins](basics-hierarchical-poisson-gamma-model.md), the variance of a biological gene in a reference cell with normalizing product $(\phi s)^* = \operatorname{median}_j \phi_j s_j$ decomposes into Poisson, technical and biological terms. Define the **biological variance contribution** of gene $i$,

$$\sigma_i = \frac{\delta_i(\theta + 1)}{\big[(\phi s)^*\mu_i\big]^{-1} + \theta + \delta_i(\theta + 1)} \in [0, 1).$$

**Detection rule.** Given a variance-contribution threshold $\gamma_H$ and an evidence threshold $\alpha_H$, gene $i$ is a highly variable gene (HVG) if its tail posterior probability

$$\pi_i^H(\gamma_H) = \Pr(\sigma_i > \gamma_H \mid \text{data}) > \alpha_H;$$

lowly variable genes use $\pi_i^L(\gamma_L) = \Pr(\sigma_i < \gamma_L \mid \text{data}) > \alpha_L$. Both are estimated by the fraction of MCMC draws satisfying the event.

**Properties.**

1. $\sigma_i > \gamma_H$ if and only if

$$\delta_i > \frac{\gamma_H}{1 - \gamma_H}\cdot\frac{\big((\phi s)^*\mu_i\big)^{-1} + \theta}{1 + \theta},$$

a contour that increases in $\gamma_H$ and decreases in the expression rate $\mu_i$, so less over-dispersion is required for highly expressed genes to be called variable.
2. *Calibration of $\alpha_H$.* With $D(\alpha) = \{i : \pi_i^H > \alpha\}$, the expected false discovery and false negative rates are

$$\mathrm{EFDR}(\alpha) = \frac{\sum_{i \in D(\alpha)} (1 - \pi_i^H)}{|D(\alpha)|}, \qquad \mathrm{EFNR}(\alpha) = \frac{\sum_{i \notin D(\alpha)} \pi_i^H}{q_0 - |D(\alpha)|},$$

and $\alpha_H$ is chosen where the two coincide (or to meet a target EFDR).

## Depends on

- [Hierarchical Poisson–gamma model with spike-in genes](basics-hierarchical-poisson-gamma-model.md)

## Expansion

Dividing the biological term $\delta_i(\theta + 1)m^2$ by the total variance $m + \theta m^2 + \delta_i(\theta+1)m^2$ at $m = (\phi s)^*\mu_i$ and cancelling $m^2$ gives $\sigma_i$. Solving $\sigma_i > \gamma$ for $\delta_i$ gives the contour in property 1. In property 2, $1 - \pi_i^H$ is the posterior probability that a selected gene is not truly above the threshold, so its average over selected genes is the posterior expected false discovery proportion; $\mathrm{EFDR}$ decreases and $\mathrm{EFNR}$ increases with $\alpha$, so a crossing point exists. The criterion uses posterior draws directly and avoids the cost of Bayes factors, and because $\theta$ is estimated jointly from spike-ins, technical over-dispersion is not mistaken for biological heterogeneity.

## Sources

- Vallejos CA, Marioni JC, Richardson S, "BASiCS: Bayesian Analysis of Single-Cell Sequencing Data" (2015), Materials and Methods, "BASiCS: detection of highly and lowly variable genes", Equations (6)–(10), <https://doi.org/10.1371/journal.pcbi.1004333>, PMCID PMC4480965.
