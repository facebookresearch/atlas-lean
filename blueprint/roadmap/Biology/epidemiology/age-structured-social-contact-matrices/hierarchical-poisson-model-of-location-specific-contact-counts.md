# Hierarchical Poisson model of location-specific contact counts

Let the participants $i$ of a contact survey belong to age groups $a_i \in \{1, \dots, K\}$, and let $X^L_{i,\alpha}$ be the number of contacts that $i$ reports on the survey day at location $L \in \{H, W, S, O\}$ (home, work, school, other) with persons in age group $\alpha$. Conditionally on the parameters, the counts are independent with

$$X^L_{i,\alpha} \sim \mathrm{Poisson}(\mu^L_{i,\alpha}),$$

$$\mu^H_{i,\alpha} = \sigma_i \lambda^H_{a_i,\alpha} (\nu_{i,\alpha} + \delta_H), \qquad \mu^W_{i,\alpha} = \sigma_i \lambda^W_{a_i,\alpha} (w_i + \delta_W),$$

$$\mu^S_{i,\alpha} = \sigma_i \lambda^S_{a_i,\alpha} (s_i + \delta_S), \qquad \mu^O_{i,\alpha} = \sigma_i \lambda^O_{a_i,\alpha},$$

where:

- $\sigma_i > 0$ is a random effect for individual $i$ (its overall sociability);
- $\nu_{i,\alpha} \in \{0, 1, 2, \dots\}$ is the number of cohabitants of $i$ in age group $\alpha$ (household age structure);
- $w_i, s_i \in \{0, 1\}$ indicate whether $i$ went to work or to school on the survey day;
- $\delta_H, \delta_W, \delta_S \ge 0$ are background contact parameters (visitors at home, work and school);
- $\lambda^L_{a,\alpha} > 0$ is the typical contact rate between age groups $a$ and $\alpha$ at location $L$, the main estimand.

The contact rates receive a smoothing hierarchical prior:

$$\log \lambda^L_{a,\alpha} = \frac{1}{|N_{a,\alpha}|} \sum_{(A, A') \in N_{a,\alpha}} \epsilon^L_{A,A'},$$

where $N_{a,\alpha}$ is the set of (up to) four age-group pairs adjacent to $(a, \alpha)$ together with $(a, \alpha)$ itself, and the $\epsilon^L_{A,A'}$ are hyperparameters.

Properties:

- for fixed $\sigma_i$, the expected number of home contacts with age group $\alpha$ is affine in the number $\nu_{i,\alpha}$ of cohabitants of that age, so home contacts grow linearly with household size (a frequency-dependent rather than density-dependent mixing assumption), with $\delta_H$ absorbing contacts with visitors;
- on a day when $i$ neither works nor attends school ($w_i = s_i = 0$), the expected work and school contacts reduce to the background terms $\sigma_i \lambda^W_{a_i,\alpha} \delta_W$ and $\sigma_i \lambda^S_{a_i,\alpha} \delta_S$;
- because $\sigma_i$ multiplies every mean of participant $i$, ratios $\mu^L_{i,\alpha} / \mu^{L'}_{i,\alpha'}$ do not depend on $\sigma_i$: individual sociability is separated from the age and location structure;
- each $\log \lambda^L_{a,\alpha}$ is an average of hyperparameters that it shares with its neighbouring cells, so the prior couples adjacent age groups and smooths the estimated matrix along both age axes.

## Expansion

Each participant contributes repeated counts across locations and age groups, which motivates the shared random effect $\sigma_i$; the population-level matrices $\lambda^L$ are then read off after integrating out the individual effects. The posterior is computed by Markov chain Monte Carlo. Fitted to the eight-country European diary survey (POLYMOD), the near-linear growth of home contacts with household size supports the frequency-dependent form of $\mu^H$, and the estimated matrices are strongly assortative by age except at work.

## Sources

- K. Prem, A. R. Cook, M. Jit, "Projecting social contact matrices in 152 countries using contact surveys and demographic data", PLoS Computational Biology 13(9) (2017) e1005697, Materials and methods, "Hierarchical model of POLYMOD contact data", Eq. (1), and Results, "Contact patterns at home", <https://doi.org/10.1371/journal.pcbi.1005697> (PMC5609774).
