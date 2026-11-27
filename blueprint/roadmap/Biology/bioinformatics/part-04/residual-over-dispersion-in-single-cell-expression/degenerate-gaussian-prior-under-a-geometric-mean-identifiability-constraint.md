# Degenerate Gaussian prior under a geometric-mean identifiability constraint

In a multiplicative count model $X_{ijk} \sim \mathrm{Poisson}(\nu_{jk}\mu_i\rho_{ijk})$ for gene $i \in \{1,\dots,q\}$, cell $j$ and batch $k$, with $\nu_{jk} \sim \mathrm{Gamma}(1/\theta_k, 1/(s_{jk}\theta_k))$ and $\rho_{ijk} \sim \mathrm{Gamma}(1/\delta_i, 1/\delta_i)$, the scale of the cell factors $s_{jk}$ and of the gene means $\mu_i$ is not identifiable. It is fixed by the restriction

$$\Big(\prod_{i=1}^q \mu_i\Big)^{1/q} = \mu_0 \iff \frac1q \sum_{i=1}^q \log\mu_i = \log\mu_0 .$$

**Proposition 1.** The prior $\mu_i \overset{\text{iid}}{\sim} \log\text{-}\mathcal N(0, a_\mu^2)$ conditioned on the restriction is

$$\log\boldsymbol\mu \sim \mathcal N_q\Big(\log(\mu_0)\,\mathbf 1_q,\; a_\mu^2\big(I_q - \tfrac1q \mathbf 1_q \mathbf 1_q'\big)\Big),$$

a degenerate normal law supported on the hyperplane of the restriction.

**Proposition 2.** For any reference gene $r$, this law factorizes as $\log\boldsymbol\mu_{-r} \sim \mathcal N_{q-1}\big(\log(\mu_0)\mathbf 1_{q-1}, a_\mu^2(I_{q-1} - \tfrac1q\mathbf 1_{q-1}\mathbf 1_{q-1}')\big)$ and a point mass

$$\log\mu_r \mid \log\boldsymbol\mu_{-r} = q\log\mu_0 - \sum_{i \ne r}\log\mu_i .$$

**Proposition 3.** For $i \ne r$, with $\boldsymbol\mu_{-i,r}$ the vector without entries $i$ and $r$,

$$\log\mu_i \mid \log\boldsymbol\mu_{-i,r} \sim \mathcal N\Big(\tfrac12\big(q\log\mu_0 - \mathbf 1_{q-2}'\log\boldsymbol\mu_{-i,r}\big),\; \tfrac12 a_\mu^2\Big).$$

## Depends on

- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)

## Expansion

With $M = \sum_i \log\mu_i$, the pair $(\log\boldsymbol\mu, M)$ is jointly normal with $\mathrm{Cov}(\log\boldsymbol\mu, M) = a_\mu^2\mathbf 1_q$ and $\mathrm{Var}(M) = q a_\mu^2$; Gaussian conditioning on $M = q\log\mu_0$ gives Proposition 1 (as in West and Harrison's Theorem 8.2). Propositions 2 and 3 follow from the Sherman–Morrison inverse $(I_m - \tfrac1q\mathbf 1\mathbf 1')^{-1} = I_m + \tfrac{1}{q-m}\mathbf 1\mathbf 1'$: for $m = q-1$ the conditional variance vanishes, and for $m = q-2$ it equals $a_\mu^2/2$. A sampler therefore updates $\log\boldsymbol\mu_{-r}$ with the conditionals of Proposition 3 and sets $\mu_r$ deterministically; choosing $r$ at random in each iteration avoids distorting posterior inference for a fixed reference gene.

## Sources

- N. Eling, A. C. Richard, S. Richardson, J. C. Marioni, C. A. Vallejos, "Correcting the mean-variance dependency for differential variability testing using single-cell RNA sequencing data", Cell Systems 7(3) (2018) 284–294, STAR Methods, Equations 37–53 and Propositions 1–3, <https://doi.org/10.1016/j.cels.2018.06.011>, PMCID PMC6167088.
