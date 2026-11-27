# Multiplicative model of the weekly effective reproduction number

Let two cross-immunizing strains be indexed by $i \in \{1,2\}$, let $t$ run over weeks, let $y_i(t) \ge 0$ be a proxy for weekly incidence of strain $i$ (for instance the fraction of laboratory tests positive for strain $i$ multiplied by the population-weighted fraction of physician visits for influenza-like illness, which is proportional to incidence up to an unknown constant), and let

$$X_i(t) \;=\; \sum_{u \le t} y_i(u)$$

be the cumulative incidence proxy, a surrogate for susceptible depletion. Let $\mathcal{R}_i(t)$ be the effective reproduction number of strain $i$ in week $t$, estimated from $y_i$ and an assumed serial interval distribution. The model is multiplicative,

$$\mathcal{R}_i(t) \;=\; A_{i,\,\mathrm{season}(t)} \cdot \exp\bigl(-\beta_{ii} X_i(t)\bigr) \cdot \exp\bigl(-\beta_{ij} X_j(t)\bigr) \cdot \exp\bigl(f_i(t)\bigr), \qquad j \ne i,$$

equivalently, with $\mathrm{season}(t)$ the epidemic season containing week $t$ and $f_i$ a spline in week-of-year,

$$\log \mathcal{R}_i(t) \;=\; \alpha_{i,\,\mathrm{season}(t)} \;-\; \beta_{ii} X_i(t) \;-\; \beta_{ij} X_j(t) \;+\; \sum_{m} b_{i,m} B_m(t),$$

fitted by least squares on $\log \mathcal{R}_i$. The coefficients are interpreted as follows: $A_{i,\cdot}$ is the strain-season baseline transmissibility, determined by the basic reproduction number and the susceptible fraction at the start of the season; $\beta_{ii} > 0$ measures self-immunity, the depletion of susceptibles by infection with the same strain; $\beta_{ij} > 0$ measures cross-immunity, the depletion attributable to the other strain; and the spline absorbs the residual seasonal forcing of transmission.

For two co-circulating human betacoronaviruses this model explains most of the variability in the weekly effective reproduction numbers (adjusted $R^2 = 74.3\%$), gives $\beta_{ij} < \beta_{ii}$ for both strains (cross-immunity is weaker per unit incidence proxy than self-immunity, but can still dominate when the cross-immunizing strain has a large outbreak), and leaves strain-season baselines that are consistent across seasons and uncorrelated with incidence in prior seasons, consistent with immunity waning within about a year. A compartmental susceptible-exposed-infectious-recovered-susceptible model with two strains, waning immunity and seasonal forcing, fitted to the same incidence proxies and reproduction numbers, reproduces them with a duration of immunity near $45$ weeks and a basic reproduction number varying between $1.7$ in summer and $2.2$ in winter, peaking in the second week of January.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)

## Remarks

The multiplicative form is the natural one because the quantities act on different factors of the same product: transmissibility per contact is modulated by season, while the chance that a contact meets a susceptible is modulated by immunity. With mass-action transmission $\mathcal{R}_i(t) = \mathcal{R}_{0,i}(t)\, S_i(t)/N$, so any model for $S_i$ of the form $S_i(t)/N = \exp(-\beta_{ii} X_i(t) - \beta_{ij} X_j(t))$, the first-order attack-rate approximation to depletion by past infection with either strain, makes $\log \mathcal{R}_i$ additive in the covariates and renders the regression linear.

Identification rests on the covariates varying on different timescales: cumulative incidence is monotone within a season and resets between seasons through waning, while the spline is periodic in week-of-year, so a persistent within-season decline in transmissibility is attributed to depletion and a repeatable annual shape to forcing. The fitted decomposition assigns the autumn rise mainly to seasonal forcing and the late-season decline mainly to susceptible depletion.

Because the incidence proxy is only proportional to incidence, with an unknown and location-dependent constant, the coefficients $\beta$ are on the proxy scale and are not directly interpretable as per-infection immunity; only their ratio, $\beta_{ij}/\beta_{ii}$, which compares cross- to self-immunization, is free of that constant.

## Sources

- S. M. Kissler, C. Tedijanto, E. Goldstein, Y. H. Grad, M. Lipsitch, "Projecting the transmission dynamics of SARS-CoV-2 through the postpandemic period", Science 368 (2020) 860-868, sections "Transmission dynamics of HCoV-OC43 and HCoV-HKU1" and the regression and transmission-model fits reported there, <https://doi.org/10.1126/science.abb5793> (PMC7164482).
