# Hierarchical Poisson–gamma model with spike-in genes

**Model.** Let $X_{ij}$ be the expression count of gene $i$ in cell $j$ ($j = 1, \dots, n$), where genes $i = 1, \dots, q_0$ are biological and $i = q_0 + 1, \dots, q$ are technical spike-in genes added in known amounts to every cell. With normalized expression rates $\mu_i$ (known, from the added amounts, for spike-ins), cell-specific mRNA-content size factors $\phi_j$ and capture-efficiency constants $s_j$,

$$X_{ij} \mid \mu_i, \phi_j, \nu_j, \rho_{ij} \sim \begin{cases} \mathrm{Poisson}(\phi_j \nu_j \mu_i \rho_{ij}), & i \le q_0,\\ \mathrm{Poisson}(\nu_j \mu_i), & i > q_0, \end{cases}$$

independently, with mutually independent random effects

$$\nu_j \mid s_j, \theta \sim \mathrm{Gamma}\big(1/\theta,\ 1/(s_j\theta)\big), \qquad \rho_{ij} \mid \delta_i \sim \mathrm{Gamma}(1/\delta_i,\ 1/\delta_i)$$

(shape–rate parametrization), so $\mathbb{E}\nu_j = s_j$, $\mathrm{Var}\,\nu_j = s_j^2\theta$, $\mathbb{E}\rho_{ij} = 1$, $\mathrm{Var}\,\rho_{ij} = \delta_i$. The single hyperparameter $\theta$ quantifies unexplained technical noise shared by all genes; the gene-specific $\delta_i$ quantify biological cell-to-cell over-dispersion.

**Proposition.** Writing $I_i = \mathbf 1[i \le q_0]$ and $m_{ij} = \phi_j^{I_i} s_j \mu_i$, the marginal moments (random effects integrated out) are

$$\mathbb{E}(X_{ij}) = m_{ij}, \qquad \mathrm{Var}(X_{ij}) = m_{ij} + \theta\, m_{ij}^2 + I_i\, \delta_i(\theta + 1)\, m_{ij}^2 .$$

For spike-in genes the marginal law is negative binomial with mean $s_j\mu_i$ and dispersion $\theta$.

## Expansion

Condition on the random effects: $X_{ij}$ is Poisson with rate $\Lambda = m_{ij}\,(\nu_j/s_j)\,\rho_{ij}^{I_i}$, so by the law of total variance $\mathrm{Var}\,X = \mathbb{E}\Lambda + \mathrm{Var}\,\Lambda$. Since $\nu_j/s_j$ and $\rho_{ij}$ are independent with mean one, $\mathbb{E}[(\nu_j/s_j)^2\rho_{ij}^2] = (1 + \theta)(1 + \delta_i)$, hence $\mathrm{Var}\,\Lambda = m_{ij}^2[(1+\theta)(1+\delta_i) - 1] = m_{ij}^2[\theta + \delta_i(1+\theta)]$ for biological genes and $m_{ij}^2\theta$ for spike-ins. The three variance terms are the Poisson baseline, the inflation due to technical noise, and biological heterogeneity. A Poisson mixed over a gamma rate is negative binomial, which gives the spike-in marginal. Because spike-ins share $\nu_j$ and $\theta$ with biological genes but not $\phi_j$ or $\delta_i$, their known input amounts identify the technical component, and $\phi_j, s_j, \theta, \delta_i, \mu_i$ are inferred jointly by MCMC (the $s_j$ are identified because the spike-in rates $\mu_i$, $i > q_0$, are known from the added amounts, while the arbitrary scale of the $\phi_j$ is fixed by the restriction $n^{-1}\sum_j \phi_j = \phi_0$).

## Sources

- Vallejos CA, Marioni JC, Richardson S, "BASiCS: Bayesian Analysis of Single-Cell Sequencing Data" (2015), Materials and Methods, "The BASiCS model", Equations (1)–(5), <https://doi.org/10.1371/journal.pcbi.1004333>, PMCID PMC4480965.
