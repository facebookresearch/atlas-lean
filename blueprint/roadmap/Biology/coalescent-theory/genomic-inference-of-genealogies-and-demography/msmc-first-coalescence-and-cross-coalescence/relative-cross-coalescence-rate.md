# Relative cross-coalescence rate

**Definition.** Sample haplotypes from two populations $1$ and $2$, and let $\lambda_1(t)$ and $\lambda_2(t)$ be the coalescence rates of pairs within population $1$ and within population $2$, and $\lambda_{12}(t)$ the coalescence rate of a pair with one lineage from each, at time $t$ before the present. The **relative cross-coalescence rate** is

$$\gamma(t) = \frac{2\lambda_{12}(t)}{\lambda_1(t) + \lambda_2(t)}.$$

**Proposition (clean split).** Suppose the two populations descend from one panmictic ancestral population that split at time $T$ with no gene flow afterwards. Then $\gamma(t) = 0$ for $t < T$ and $\gamma(t) = 1$ for $t > T$.

**Estimation.** In the multiple sequentially Markovian coalescent with haplotypes from both populations, each time segment $i$ carries three rates $\lambda_{1,i}, \lambda_{12,i}, \lambda_{2,i}$, estimated by expectation-maximization with the constraint $\gamma_i \le 1$, and $\gamma_i = 2\lambda_{12,i}/(\lambda_{1,i}+\lambda_{2,i})$. The time at which $\gamma$ crosses $1/2$ is a natural summary of a split time. Applied to four haplotypes per population pair, this dated a gradual separation of West African and non-African ancestors from before $200$ kya until about $40$ kya.

## Depends on

- [MSMC: first-coalescence hidden Markov model](msmc-first-coalescence-hidden-markov-model.md)

## Expansion

After the split (between $0$ and $T$) a cross-population pair can only coalesce once both lineages are traced back beyond $T$, so $\lambda_{12} = 0$ while the within-population rates are positive. Before the split all lineages lie in the same panmictic population, so every pair coalesces at the same rate and $\lambda_{12} = \lambda_1 = \lambda_2$, giving $\gamma = 1$. Normalizing by the mean within-population rate removes the effect of population size changes, which affect all three rates; this is why $\gamma$ isolates separation from demography. Phasing switch errors break long shared haplotypes between populations and bias recent $\gamma$ estimates, so unphased sites are removed for this analysis.

Outside the clean split, $\gamma$ is read qualitatively. In the source's simulations, a split followed by migration gives higher values of $\gamma$ after the split than a clean split does, and a gradual decline of $\gamma$ from $1$ to $0$ indicates a separation spread over time rather than a single split. Gene flow does not by itself force $0 < \gamma(t) < 1$ at every $t < T$: after a single admixture pulse at time $t_p < T$, cross-population pairs still cannot coalesce more recently than $t_p$, so $\gamma(t) = 0$ for $t < t_p$.

## Sources

- S. Schiffels and R. Durbin, "Inferring human population size and separation history from multiple genome sequences", Nature Genetics 46 (2014), Results and Online Methods ("Parameter Inference"), <https://doi.org/10.1038/ng.3015> (PMC4116295).
