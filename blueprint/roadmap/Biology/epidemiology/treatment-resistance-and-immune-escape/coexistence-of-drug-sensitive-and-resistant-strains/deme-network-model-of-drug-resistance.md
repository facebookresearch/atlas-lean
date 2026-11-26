# Deme-network model of drug resistance and robust strain coexistence

Generalize the [two-deme model](two-deme-reproductive-numbers-and-coexistence.md) to $M$ equal demes connected by a symmetric adjacency matrix $\Delta$ ($\Delta_{ij} = 1$ if infected individuals in deme $i$ can infect individuals in deme $j$; the graph is connected). Each deme is either treated ($T_i = 1$) or untreated ($T_i = 0$). With within-deme rate $\kappa$, between-deme rate $\beta \le \kappa$, recovery rate $g$, treatment efficacy $\epsilon$ against the sensitive strain and resistance cost $c$, the proportions $w_i, r_i$ of deme $i$ infected with the sensitive and resistant strains satisfy

$$\dot w_i = \Big(\kappa (1 - \epsilon T_i) w_i + \beta \sum_j \Delta_{ji} (1 - \epsilon T_j) w_j\Big)(1 - w_i - r_i) - g w_i,$$

$$\dot r_i = (1 - c)\Big(\kappa r_i + \beta \sum_j \Delta_{ji} r_j\Big)(1 - w_i - r_i) - g r_i.$$

Linearizing at the infection-free state gives the strain reproductive numbers

$$R_0^{r} = \frac{(1-c)\big(\kappa + \beta\, \rho(\Delta)\big)}{g}, \qquad R_0^{w} = \frac{\rho\big((\kappa I + \beta \Delta^{\top})\, D_\epsilon\big)}{g}, \quad D_\epsilon = \operatorname{diag}(1 - \epsilon T_i),$$

where $\rho$ is the spectral radius; on a $d$-regular deme graph $\rho(\Delta) = d$. On random regular and small-world deme graphs, coexistence of both strains, including robust coexistence in which at least 80% of demes carry at least 10% of each strain, occurs over broad ranges of treatment coverage and cost. Untreated neighboring demes can differ widely in resistance frequency, and graphs with the same overall treatment level can give very different overall resistance.

## Depends on

- [Two-deme model of drug resistance: strain reproductive numbers and coexistence](two-deme-reproductive-numbers-and-coexistence.md)
- [Competitive exclusion of drug-sensitive and resistant strains under partial treatment](competitive-exclusion-under-partial-treatment.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Proof sketch

The resistant strain's linearization is $\dot r = \big((1-c)(\kappa I + \beta \Delta^{\top}) - g I\big) r$, whose leading eigenvalue is $(1-c)(\kappa + \beta \rho(\Delta)) - g$. The sensitive strain's is $\dot w = \big((\kappa I + \beta\Delta^{\top}) D_\epsilon - g I\big) w$. The reproductive numbers are the spectral radii of the corresponding next-generation matrices, divided by $g$. In the study, between-deme rates are scaled by deme size so that results do not depend on population size. The coexistence and heterogeneity results are numerical. With baseline cost $c = 0.2$, treatment of 20–40% of demes supported robust coexistence in some structures. About a third of untreated neighbor pairs differed by more than 10 percentage points in resistance frequency, with differences up to 60 points in individual runs. In a LASSO analysis over Watts–Strogatz graphs, a deme's own treatment status and its neighbors' treatment were the strongest local predictors. High degree and centrality push a deme toward the strain that is more common overall. Longer mean path length favors coexistence, while higher network efficiency hinders it. Raising $\beta/\kappa$ or adding edges brings the system closer to the well-mixed case, where [competitive exclusion](competitive-exclusion-under-partial-treatment.md) holds.

## Sources

- M. S. Krieger, C. E. Denison, T. L. Anderson, M. A. Nowak and A. L. Hill, "Population structure across scales facilitates coexistence and spatial heterogeneity of antibiotic-resistant infections", PLoS Computational Biology 16 (2020) e1008010, Results ("Robust coexistence in more complex population structures", "Large differences in resistance levels are possible even between connected regions", "Properties contributing to higher resistance", Figure 4, Table 1) and Methods ("Model equations", Equation 3), <https://doi.org/10.1371/journal.pcbi.1008010>, PMCID: PMC7365476.
