# Pure-birth likelihood with a rate-shift window

Let a reconstructed ultrametric phylogeny with $n$ tips have branching times $t_1 > t_2 > \dots > t_{n-1}$ before the present, and let $k(t)$ be the number of lineages present at time $t$. Under a pure-birth process with piecewise-constant speciation rate

$$\lambda(t) = \begin{cases} \lambda_2, & t \in [t_b, t_a] \text{ (the shift window)}, \\ \lambda_1, & \text{otherwise}, \end{cases}$$

the likelihood of the branching times after the root, conditional on two lineages at the root and up to a factor not depending on $(\lambda_1, \lambda_2)$, is

$$L(\lambda_1, \lambda_2) = \prod_{i=2}^{n-1} \lambda(t_i)\, \exp\!\left(-\int_0^{t_1} k(t)\, \lambda(t)\, dt\right).$$

With $m_W$ and $m_O$ the numbers of branching events after the root inside and outside the window ($m_W + m_O = n - 2$), and $\ell_W = \int_{[t_b, t_a]} k(t)\, dt$ and $\ell_O = \int_{[0, t_1] \setminus [t_b, t_a]} k(t)\, dt$ the total branch lengths inside and outside it:

1. the maximum-likelihood estimates are $\hat\lambda_2 = m_W / \ell_W$ and $\hat\lambda_1 = m_O / \ell_O$;
2. the constant-rate model is the case $\lambda_1 = \lambda_2$, with estimate $(n - 2)/(\ell_W + \ell_O)$; twice the log-likelihood ratio between the shift model and the constant model is referred to a $\chi^2_1$ distribution.

## Depends on

- [Pybus–Harvey gamma statistic](pybus-harvey-gamma-statistic.md)

## Expansion

Forward in time, splits occur as an inhomogeneous Poisson process with intensity $k(t)\lambda(t)$; the density of the observed splits is the product of intensities at the event times times the probability of no further events, $\exp(-\int k\lambda)$. The factor $k(t_i)$ from choosing which lineage splits does not involve the rates and is dropped. Taking logarithms separates the two rates: $m_W \log\lambda_2 - \lambda_2 \ell_W$ and $m_O \log\lambda_1 - \lambda_1 \ell_O$, each maximized at events divided by exposure. The shift-window test was applied to cetaceans for two episodes of ocean restructuring (35–31 and 13–4 million years ago), comparing constant-rate pure-birth and birth–death models with models where the speciation rate in the window is free; extinction was dropped from the final model because its estimates tended to zero and could not be separated from speciation within short windows. Rates were higher during the restructuring periods.

## Sources

- M. E. Steeman, M. B. Hebsgaard, R. E. Fordyce, et al., "Radiation of extant cetaceans driven by restructuring of the oceans", Systematic Biology (2009), METHODS (discrete-shift likelihood models and likelihood-ratio test) and RESULTS AND DISCUSSION, <https://doi.org/10.1093/sysbio/syp060> (PMC2777972).
