# GLM parameterization of discrete phylogeographic diffusion

Let a discrete trait (for example, sampling location) take values in $\{1,\dots,L\}$ and evolve along the branches of a time-scaled phylogeny as a continuous-time Markov chain with overall rate $\mu > 0$ and relative rate matrix $\Lambda$. Given $P$ predictors, each an $L \times L$ array $x_{\cdot\cdot p}$ of real values for ordered pairs $i \ne j$ (typically log-transformed and standardized, for example origin population, destination population or geographic distance), the **generalized linear model (GLM)** parameterization sets

$$\Lambda_{ij} = \exp\Big(\sum_{p=1}^{P} \delta_p\, \beta_p\, x_{ijp}\Big) \quad (i \ne j), \qquad \Lambda_{ii} = -\sum_{j \ne i} \Lambda_{ij},$$

with coefficients $\beta_p \in \mathbb{R}$ and inclusion indicators $\delta_p \in \{0,1\}$, given independent priors $\delta_p \sim \mathrm{Bernoulli}(q)$ (Bayesian stochastic search variable selection).

**Properties.**

1. For every $\beta \in \mathbb{R}^P$ and $\delta \in \{0,1\}^P$, $\mu\Lambda$ is a valid rate matrix: off-diagonal entries are positive and rows sum to $0$.
2. Holding other predictors fixed, a unit increase of an included predictor $x_{ijp}$ multiplies the transition rate $i \to j$ by $e^{\beta_p}$.
3. The Bayes factor for including predictor $p$ is the ratio of posterior to prior inclusion odds,

$$\mathrm{BF}_p = \frac{\Pr(\delta_p = 1 \mid D)\,/\,\Pr(\delta_p = 0 \mid D)}{q/(1-q)} .$$

## Depends on

- [GTR matrix is a rate matrix](../../time-reversible-nucleotide-substitution-models/is-rate-matrix-gtr-rate.md)

## Remarks

Positivity holds because the exponential is positive, and the diagonal is defined to make rows sum to zero. On the log scale the rates are linear in the included predictors, which is what makes the model a GLM; the indicators let the posterior mass concentrate on a sparse set of predictors, and the posterior inclusion probability, compared with its prior, measures support for each predictor. Inference integrates over the unknown phylogeny, so predictor support accounts for phylogenetic uncertainty. In an analysis of the 2013–2016 West African Ebola epidemic (56 administrative regions), the GLM identified population sizes and geographic distance as main predictors of viral dispersal.

## Sources

- M. A. Suchard, P. Lemey, G. Baele, D. L. Ayres, A. J. Drummond and A. Rambaut, "Bayesian phylogenetic and phylodynamic data integration using BEAST 1.10", Virus Evolution 4 (2018) vey016, Section 2 ("Data integration", discrete trait models with predictors) and Section 4.1 (Ebola example), <https://doi.org/10.1093/ve/vey016>, PMCID PMC6007674.
- P. Lemey, A. Rambaut, T. Bedford et al., "Unifying viral genetics and human transportation data to predict the global transmission dynamics of human influenza H3N2", PLoS Pathogens 10 (2014) e1003932, <https://doi.org/10.1371/journal.ppat.1003932>.
