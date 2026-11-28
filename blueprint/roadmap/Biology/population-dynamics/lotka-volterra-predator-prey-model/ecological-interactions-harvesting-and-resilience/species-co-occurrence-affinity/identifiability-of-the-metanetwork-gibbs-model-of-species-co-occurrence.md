# Identifiability of the metanetwork Gibbs model of species co-occurrence

**Model.** A metanetwork $G^\star = (V^\star, E^\star)$ records the potential trophic or non-trophic interactions among $N$ species. At locations $l = 1, \dots, L$, let $X_{i,l} \in \{0,1\}$ indicate presence of species $i$. Without environmental covariates, the joint distribution at location $l$ is the Gibbs (Ising-type) law

$$
\mathbb{P}_{\psi_l}\big(\{X_{i,l}\}_{i}\big) = \frac{1}{Z_{\psi_l}}\exp\Big(\sum_{i \in V^\star}(a_i + a_l)X_{i,l} + \beta_{l}^{\mathrm{p}}\sum_{(i,j)\in E^\star} X_{i,l}X_{j,l} + \beta_{l}^{\mathrm{a}}\sum_{(i,j)\in E^\star}(1 - X_{i,l})(1 - X_{j,l})\Big),
$$

with species effects $a_i$, location effects $a_l$, a co-presence strength $\beta_l^{\mathrm{p}}$ and a co-absence strength $\beta_l^{\mathrm{a}}$ for interacting pairs. Locations are independent, so the global law is $\mathbb{P}_\psi = \prod_l \mathbb{P}_{\psi_l}$, with $\psi = (\{a_i\}_i, \{a_l, \beta_l^{\mathrm{p}}, \beta_l^{\mathrm{a}}\}_l)$. Write $\deg(i)$ for the degree of species $i$ in $G^\star$. (In the full model the effects $a_i$ also depend on environmental covariates, which separates abiotic from biotic effects on species distributions.)

**Proposition (identifiable combinations).** $\mathbb{P}_\psi$ determines uniquely, for every species $i$ and location $l$,

$$
\beta_l^{\mathrm{p}} + \beta_l^{\mathrm{a}} \qquad\text{and}\qquad a_i + a_l + \beta_l^{\mathrm{p}}\deg(i) \quad\big(\text{equivalently } a_i + a_l - \beta_l^{\mathrm{a}}\deg(i)\big).
$$

If moreover two species have different degrees in $G^\star$, then $\mathbb{P}_\psi$ also determines the differences $\beta_l^{\mathrm{a}} - \beta_{l'}^{\mathrm{a}}$ (equivalently $\beta_l^{\mathrm{p}} - \beta_{l'}^{\mathrm{p}}$) and $a_l - a_{l'}$ for all locations $l, l'$.

**Corollary (identifiability up to a two-parameter equivalence).** If two species have different degrees, then $\mathbb{P}_\psi = \mathbb{P}_{\tilde\psi}$ implies that $\tilde\psi$ lies in the equivalence class

$$
[\psi] = \big\{\big(\{a_i + \gamma\deg(i) - \delta\}_i,\ \{a_l + \delta,\ \beta_l^{\mathrm{p}} - \gamma,\ \beta_l^{\mathrm{a}} + \gamma\}_l\big) : \gamma, \delta \in \mathbb{R}\big\},
$$

and every class contains a unique representative for which the least-squares regression of $\{a_i\}$ on $\{\deg(i)\}$ has zero slope and zero intercept.

## Expansion

Expanding $(1 - X_i)(1 - X_j) = 1 - X_i - X_j + X_iX_j$ shows that the co-absence term contributes $\beta_l^{\mathrm{a}}$ to the pair coefficient of $X_iX_j$, $-\beta_l^{\mathrm{a}}\deg(i)$ to the single-site coefficient of $X_i$, and a constant absorbed into $Z_{\psi_l}$. The Gibbs law on $\{0,1\}^{V^\star}$ is thus an exponential family whose natural parameters, the field $a_i + a_l - \beta_l^{\mathrm{a}}\deg(i)$ and the pair coupling $\beta_l^{\mathrm{p}} + \beta_l^{\mathrm{a}}$, are identifiable from ratios of probabilities of configurations. Recovering the original parameters from these leaves the freedom to shift a constant between $a_i$ and $a_l$ ($\delta$) and to trade co-presence against co-absence while compensating by a degree-proportional shift of $a_i$ ($\gamma$). Degree heterogeneity pins down differences across locations. Fixing the representative orthogonal to degree makes $a_i$ interpretable as the species' intrinsic, network-independent tendency to occur, and $\beta^{\mathrm{p}}, \beta^{\mathrm{a}}$ as the net effect of biotic interactions along an environmental gradient.

## Sources

- Marc Ohlmann, Catherine Matias, Giovanni Poggiato, Stéphane Dray et al., "Quantifying the overall effect of biotic interactions on species distributions along environmental gradients", arXiv (2021), Supplementary Section S.2 (Gibbs distribution, Proposition 1, Definition 1, Corollary 1, Proposition 2), <https://doi.org/10.48550/arXiv.2103.10433>.
