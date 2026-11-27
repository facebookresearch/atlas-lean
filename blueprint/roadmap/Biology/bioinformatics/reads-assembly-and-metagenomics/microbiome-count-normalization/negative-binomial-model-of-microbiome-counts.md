# Negative binomial model of microbiome counts

Let $K_{ij} \in \{0,1,2,\dots\}$ be the number of reads assigned to taxon (OTU) $i$ in sample $j$. Let $s_j > 0$ be a known or estimated **size factor** of sample $j$ (proportional to its library size), let $\mu_i > 0$ be the mean relative abundance of taxon $i$ among biological replicates, and let $\phi_i \ge 0$ be a taxon-specific **dispersion**. The gamma-Poisson (negative binomial) model is the hierarchy

$$\Lambda_{ij} \sim \mathrm{Gamma}\big(\text{shape } 1/\phi_i,\ \text{scale } \phi_i \mu_i\big), \qquad K_{ij} \mid \Lambda_{ij} \sim \mathrm{Poisson}(s_j \Lambda_{ij}),$$

with the convention that $\phi_i = 0$ means $\Lambda_{ij} = \mu_i$ almost surely.

**Proposition.** Under this model $K_{ij}$ is negative binomial with

$$\mathbb{E}[K_{ij}] = s_j \mu_i, \qquad \operatorname{Var}(K_{ij}) = s_j \mu_i + \phi_i\, s_j^2 \mu_i^2 ,$$

and it reduces to $\mathrm{Poisson}(s_j\mu_i)$ when $\phi_i = 0$. Consequently the observed proportion $K_{ij}/s_j$ has mean $\mu_i$ and variance

$$\operatorname{Var}\!\left(\frac{K_{ij}}{s_j}\right) = \frac{\mu_i}{s_j} + \phi_i \mu_i^2 ,$$

which depends on the library size (heteroscedasticity) and does not vanish as $s_j \to \infty$ when $\phi_i > 0$.

## Depends on

- [Negative-binomial offspring probabilities](../../../epidemiology/superspreading-and-negative-binomial-offspring/nb-pmf.md)

## Remarks

The gamma variable has mean $\mu_i$ and variance $\phi_i \mu_i^2$. By the laws of total expectation and variance, $\mathbb{E}[K_{ij}] = s_j \mathbb{E}[\Lambda_{ij}] = s_j\mu_i$ and $\operatorname{Var}(K_{ij}) = \mathbb{E}[s_j\Lambda_{ij}] + \operatorname{Var}(s_j \Lambda_{ij}) = s_j\mu_i + s_j^2\phi_i\mu_i^2$; integrating the Poisson mass function against the gamma density gives the negative binomial law. The first variance term is technical (sampling) noise, which shrinks relative to the mean as the library grows; the second is biological variation among replicates, which does not. Ignoring $\phi_i > 0$ (testing proportions or Poisson counts directly) underestimates the variance and inflates false positives in differential-abundance tests. Pooling dispersion estimates across taxa through a mean-dispersion trend, as done in RNA-seq software, stabilizes the estimate of $\phi_i$ with few replicates.

## Sources

- P. J. McMurdie and S. Holmes, "Waste not, want not: why rarefying microbiome data is inadmissible", PLoS Computational Biology 10 (2014) e1003531, Introduction, Equation (1), and Results (overdispersion survey), <https://doi.org/10.1371/journal.pcbi.1003531>, PMCID PMC3974642.
