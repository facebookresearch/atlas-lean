# Gravity model of commuting flows

**Model.** Let municipalities (or other spatial units) $i$ have resident populations $N_i$ and pairwise distances $d_{ij} > 0$. The gravity model specifies the expected commuting flow from $i$ to $j \ne i$ as

$$T_{ij} = \theta\, \frac{N_i^{\tau_f}\, N_j^{\tau_t}}{d_{ij}^{\rho}},$$

with proportionality constant $\theta > 0$, exponents $\tau_f, \tau_t \ge 0$ tuning the dependence on donor and recipient sizes, and distance exponent $\rho > 0$. The probability that a commuter resident in $i$ works or studies in $j$ is then $T_{ij}/\sum_{l \ne i} T_{il}$. Fitted to Italian census commuting data, $\tau_f = 0.28$, $\tau_t = 0.66$ and $\rho = 2.95$; an exponential distance decay $e^{-d_{ij}/r}$ is a common alternative.

**Properties.**

1. Taking logarithms, $\log T_{ij} = \log\theta + \tau_f \log N_i + \tau_t \log N_j - \rho \log d_{ij}$, so the parameters can be estimated by (Poisson or least-squares) regression of log flows on log populations and log distances.
2. The destination-choice probabilities $T_{ij}/\sum_{l} T_{il}$ do not depend on $\theta$ or $\tau_f$; these affect only the total outflow from $i$, $\theta N_i^{\tau_f}\sum_{l \ne i} N_l^{\tau_t} d_{il}^{-\rho}$.
3. Flows are symmetric ($T_{ij} = T_{ji}$ for all pairs) if and only if $\tau_f = \tau_t$ (when population sizes differ).

## Expansion

Properties 1–3 follow directly from the multiplicative form. In spatial epidemic models the gravity model either generates the commuting network explicitly (assigning workplaces to synthetic individuals so that the distribution of travel distances matches census data) or enters as a distance kernel weighting the force of infection exerted by an infective at distance $d$ on each susceptible. In a metapopulation model, commuting flows between adjacent subpopulations enter through a time-scale separation that replaces explicit commuting by an effective force of infection in each subpopulation, while long-range flights move individuals stochastically with multinomially distributed passenger numbers.

## Sources

- Ajelli M, Gonçalves B, Gonçalves B, Balcan D, Colizza V, Hu H, Ramasco JJ, Merler S, Vespignani A, "Comparing large-scale computational approaches to epidemic modeling: agent-based versus structured metapopulation models" (2010), Methods, Equation (1) (gravity model and fitted exponents) and the description of the distance kernel and the metapopulation mobility layers, <https://doi.org/10.1186/1471-2334-10-190>, PMCID PMC2914769.
- D. Balcan, V. Colizza, B. Gonçalves, H. Hu, J. J. Ramasco and A. Vespignani, "Multiscale mobility networks and the spatial spreading of infectious diseases", Proceedings of the National Academy of Sciences USA 106 (2009) 21484–21489, <https://doi.org/10.1073/pnas.0906910106>.
