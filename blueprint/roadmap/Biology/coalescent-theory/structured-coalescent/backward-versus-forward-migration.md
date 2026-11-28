# Backward migration probabilities from forward migration and deme sizes

Consider demes $1, \dots, d$ with $N_1, \dots, N_d$ adults, in which, each generation, a newborn in deme $j$ is produced by a parent in deme $i$ at rate proportional to $N_i f_{ij}$, where $f_{ij} \ge 0$ is the forward per-capita contribution of deme $i$ to the offspring of deme $j$. Tracing a lineage sampled in deme $j$ one generation back, Bayes' rule gives the probability that its parent lived in deme $i$:

$$b_{ji} = \frac{N_i f_{ij}}{\sum_k N_k f_{kj}}.$$

These backward probabilities, not the forward contributions, are the migration probabilities of the structured coalescent, and $b_{ji} = f_{ij}$ fails in general: the backward matrix depends on the deme sizes. This is the relation between forward and backward migration rates of Bürger (2014, Section 3.2) under constant deme proportions. In the island–mainland model, a fraction $m$ of the island's individuals have parents from the mainland, so a lineage sampled on the island moves to the mainland with probability $m$ per generation, while migrants from the small island are a negligible fraction of the large mainland and are ignored for lineages sampled there; with coalescence probability $1/(2N_I)$ per generation on the island, two island lineages coalesce before either migrates with probability $\frac{1/(2N_I)}{1/(2N_I) + 2m}$ when $m \ll 1$, which gives $F_{IM} = 1/(1 + 4N_I m)$ (compare [Wright's $F_{ST} = 1/(1 + 4Nm)$](../../population-genetics/wright-s-island-model/tendsto-island-equilibrium.md) for the island model), Wright's (1931) value for an island receiving a fraction $m$ of migrants each generation. In the island model with equal deme sizes and symmetric exchange, the backward rates are symmetric, as in the two-lineage island rates.

## Depends on

- [Transition rates of the two-lineage structured coalescent](../../../Biology/coalescent-theory/structured-coalescent/rate.md)

## Expansion

1. A forward model with deme sizes and per-capita contributions, and the backward one-generation transition probabilities of a lineage by Bayes' rule.
2. The coalescent scaling of the backward probabilities into migration rates of the structured coalescent.
3. Equal sizes with symmetric contributions as a case where forward and backward descriptions agree, and the island–mainland model as a case where they do not.
4. The coalescence-before-migration probability and the resulting $F_{IM}$ in the island–mainland model.

## Sources

- R. Bürger, A survey of migration-selection models in population genetics, Discrete Contin. Dyn. Syst. Ser. B 19 (2014), 883–959, Section 3.2 (The relation between forward and backward migration rates). <https://doi.org/10.3934/dcdsb.2014.19.883>
- S. Wright, Evolution in Mendelian populations, Genetics 16 (1931), 97–159. <https://doi.org/10.1093/genetics/16.2.97>
