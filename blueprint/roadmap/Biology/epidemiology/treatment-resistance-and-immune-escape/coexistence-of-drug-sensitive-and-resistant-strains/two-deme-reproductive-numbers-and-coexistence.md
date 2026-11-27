# Two-deme model of drug resistance: strain reproductive numbers and coexistence

Split the population of the [partial-treatment model](competitive-exclusion-under-partial-treatment.md) into two equal demes. Every individual in one deme is treated whenever infected and nobody in the other deme is. Transmission occurs at rate $\kappa$ within a deme and at rate $\beta$ between demes, with $0 \le \beta \le \kappa$. With $w_u, r_u$ the proportions of the untreated deme infected with the sensitive and resistant strains, and $w_t, r_t$ the same for the treated deme,

$$\dot w_u = \tfrac12\big(\kappa w_u + \beta (1-\epsilon) w_t\big)(1 - w_u - r_u) - g w_u, \qquad \dot w_t = \tfrac12\big(\beta w_u + \kappa (1-\epsilon) w_t\big)(1 - w_t - r_t) - g w_t,$$

$$\dot r_u = \tfrac12 (1-c)\big(\kappa r_u + \beta r_t\big)(1 - w_u - r_u) - g r_u, \qquad \dot r_t = \tfrac12 (1-c)\big(\beta r_u + \kappa r_t\big)(1 - w_t - r_t) - g r_t.$$

The next-generation method gives the strain reproductive numbers

$$R_0^{w} = \frac{\kappa (2 - \epsilon) + \sqrt{\kappa^2 \epsilon^2 + 4 (1 - \epsilon) \beta^2}}{4 g}, \qquad R_0^{r} = \frac{(1 - c)(\kappa + \beta)}{2 g}.$$

Unlike the well-mixed case, comparing $R_0^w$ with $R_0^r$ no longer determines the outcome. Besides equilibria with only one strain, the system has a stable equilibrium in which both strains coexist, and coexist within each deme. In numerical exploration with $\epsilon = 0.9$ this occurs only for weak between-deme coupling ($\beta/\kappa < 0.7$) and intermediate costs of resistance $c$.

## Depends on

- [Competitive exclusion of drug-sensitive and resistant strains under partial treatment](competitive-exclusion-under-partial-treatment.md)
- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [The spectrum of a real 2 × 2 matrix is its set of characteristic roots](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/mem-spectrum-iff-is-char-root.md)

## Proof sketch

At the infection-free state the sensitive strain's next-generation matrix is $\frac{1}{2g}\begin{pmatrix} \kappa & \beta(1-\epsilon) \\ \beta & \kappa(1-\epsilon) \end{pmatrix}$, with trace $\kappa(2-\epsilon)/(2g)$ and determinant $(1-\epsilon)(\kappa^2 - \beta^2)/(4g^2)$. Its largest eigenvalue is the stated $R_0^w$, since the discriminant simplifies to $\kappa^2 \epsilon^2 + 4(1-\epsilon)\beta^2$. The resistant strain's matrix $\frac{1-c}{2g}\begin{pmatrix} \kappa & \beta \\ \beta & \kappa \end{pmatrix}$ has largest eigenvalue $(1-c)(\kappa+\beta)/(2g)$. For $\epsilon = 0$ the two formulas agree up to the factor $1 - c$, and for $\beta = \kappa$ the population is effectively well mixed with $f = 1/2$. With preferential within-deme mixing, a strain that is globally disfavored can still be locally favored: the resistant strain in the treated deme and the sensitive strain in the untreated deme. Cross-deme transmission then keeps each strain present in both demes. The paper derives the coexistence boundaries in its supplement and reports the region as small even for this extreme clustering of treatment; the numbers above are from those numerical results.

## Sources

- M. S. Krieger, C. E. Denison, T. L. Anderson, M. A. Nowak and A. L. Hill, "Population structure across scales facilitates coexistence and spatial heterogeneity of antibiotic-resistant infections", PLoS Computational Biology 16 (2020) e1008010, Results ("Limited coexistence in two connected subpopulations with heterogeneous treatment distribution", Figure 3D–G) and Methods ("Model equations", Equation 2), <https://doi.org/10.1371/journal.pcbi.1008010>, PMCID: PMC7365476.
