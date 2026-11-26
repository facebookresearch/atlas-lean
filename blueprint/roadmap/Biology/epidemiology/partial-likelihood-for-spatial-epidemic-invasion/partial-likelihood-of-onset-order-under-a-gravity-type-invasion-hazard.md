# Partial likelihood of onset order under a gravity-type invasion hazard

Let $N$ locations have epidemic onset times $t_1, \dots, t_N$ (assumed distinct), population sizes
$N_j > 0$ and pairwise connection weights $d_{ij} > 0$ (geographic distance, or a mobility flow
such as commuters or air passengers). For each location $j$ let $\mathcal I_{t_j}$ be the set of
locations already infected before $t_j$. Model the conditional intensity of onset in $j$ as

$$\lambda(t_j \mid \mathcal H_{t_j}) = \lambda_0(t_j)\left[ N_j^{\mu}\,
\frac{\sum_{i \in \mathcal I_{t_j}} d_{ij}^{\gamma}}{\big(\sum_{k \ne j} d_{jk}^{\gamma}\big)^{\varepsilon}}
+ \rho \right],$$

with an arbitrary positive baseline hazard $\lambda_0$, population exponent $\mu$, connectivity
exponent $\gamma$ (replaced by $-\gamma$ when $d$ is a distance, so that $\gamma > 0$ means risk
decays with distance), normalization exponent $\varepsilon \in [0,1]$ and external seeding rate
$\rho \ge 0$. The probability that, among all locations still at risk at $t_j$, it is $j$ that is
invaded is

$$P_j = \frac{\lambda(t_j \mid \mathcal H_{t_j})}{\sum_{k:\, t_k \ge t_j} \lambda(t_k \mid \mathcal H_{t_j})},$$

where the risk-set intensities are evaluated with the same history. The factor $\lambda_0(t_j)$
cancels, and $(\mu, \gamma, \varepsilon, \rho)$ are estimated by maximizing the partial
log-likelihood

$$L_p = \sum_{j=1}^{N} \log P_j .$$

## Expansion

This is Cox's partial likelihood applied to a spatio-temporal point process: conditioning on the
observed onset times leaves only the information in their order, so the time-varying baseline
(seasonal forcing, climate, reporting) is an infinite-dimensional nuisance parameter that need not
be modelled. The bracket is a gravity-type force of infection. $\mu > 0$ means larger cities are
invaded preferentially (hierarchical spread). $\varepsilon = 0$ gives density-dependent pressure,
summing contributions of all infected neighbours, while $\varepsilon = 1$ gives
density-independent pressure, the weighted fraction of a city's neighbours that are infected.
Different choices of $d_{ij}$ are compared by the Akaike information criterion of the maximized
partial likelihood; in the source, work-commute flows explain US influenza onset order better than
air traffic or geographic distance.

## Sources

- V. Charu, S. Zeger, J. Gog, O. N. Bjørnstad, S. Kissler, L. Simonsen, B. T. Grenfell, C. Viboud,
  "Human mobility and the spatial transmission of influenza in the United States", PLoS
  Computational Biology 13 (2017) e1005382, Materials and Methods, "Semi-parametric mechanistic
  model of the infectious process", <https://doi.org/10.1371/journal.pcbi.1005382> (PMC5349690).
