# Wedding-cake genealogy and the leave-one-out composite likelihood

**Setting.** In the [SMCSD hidden Markov model](smcsd-hidden-markov-model-with-variable-population-size.md), the trunk genealogy absorbs the new lineage at total rate $n/\lambda(t)$ at every time $t$. In the true coalescent the number $A_n(t)$ of lineages ancestral to the $n$ observed haplotypes decreases, and a new lineage is absorbed at rate $A_n(t)/\lambda(t)$.

**Proposition (bias of the trunk).** Because $A_n(t) \le n$, with $\mathbb{E}[A_n(t)] < n$ for every $t > 0$ when $n \ge 2$, the constant trunk makes absorption too fast, so absorption events concentrate in the recent past; when $\lambda$ is estimated from the inferred distribution of absorption times, few events fall in the middle and ancient past and ancient population sizes are overestimated. Recent sizes are almost unaffected, since $A_n(t) \approx n$ for small $t$.

**Wedding-cake correction.** Partition time into intervals $D_i = [t_{i-1}, t_i)$ and, on $D_i$, replace the absorption multiplicity $n$ by

$$\bar n(t_{i-1}) = \mathbb E\big[A_n(t_{i-1})\big],$$

computed under the coalescent with history $\lambda$, while keeping the haplotype weights $n_h/n$ unchanged, so that every trunk lineage can still absorb at all times and only the absorption rate varies with time. For $n = 1$ (two sequences) $\bar n \equiv 1$ and the model is unchanged.

**Leave-one-out composite likelihood.** To use all haplotypes symmetrically, each is left out in turn and conditioned on the others:

$$L_{\mathrm{LCL}}(\lambda; h_1, \dots, h_n) = \prod_{i=1}^n\hat\pi^{(\lambda)}_{\mathrm{SMC}}\big(h_i \mid h_1, \dots, h_{i-1}, h_{i+1}, \dots, h_n\big),$$

maximized over a piecewise-constant $\lambda$ by expectation-maximization, with adjacent intervals tied to avoid over-fitting where few absorption events occur.

## Depends on

- [SMCSD hidden Markov model with variable population size](smcsd-hidden-markov-model-with-variable-population-size.md)
- [Tavaré's formula](../../ancestral-lineage-counting-and-tavar-s-formula/exp-block-counting-generator-apply.md)
- [The PAC likelihood is normalized but need not be exchangeable](../../../population-structure/li-stephens-haplotype-copying-model/product-of-approximate-conditionals-pac-likeliho.md)

## Expansion

Under a variable-size coalescent the block-counting process $A_n$ is a time-changed Kingman death process, so $\mathbb E[A_n(t)]$ follows from Tavaré's formula evaluated at the scaled time $\int_0^t d\tau/\lambda(\tau)$. The name describes the trunk drawn with thickness proportional to $\bar n$: piecewise constant and decreasing back in time. The leave-one-out product is a composite likelihood rather than a joint likelihood: unlike a product of approximate conditionals in a fixed order, it treats all haplotypes alike, but its factors are not conditionally independent, so its curvature does not give calibrated standard errors.

## Sources

- S. Sheehan, K. Harris and Y. S. Song, "Estimating variable effective population sizes from multiple genomes: a sequentially Markov conditional sampling distribution approach", Genetics 194 (2013), section "Modifying the Trunk Genealogy", Equations (13)–(14) and Figures 3 and 8, <https://doi.org/10.1534/genetics.112.149096> (PMC3697970).
