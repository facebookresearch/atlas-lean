# Numerical parameter identifiability on a level-1 network from quartet CFs

Let $\widetilde{\mathcal{N}}$ be a level-1 metric binary semidirected phylogenetic network on a taxon set
$X$ with $|X| \ge 4$ and no $2$-cycles, with numerical parameters the edge lengths and the hybridization
probabilities. Under the network multispecies coalescent with one gene lineage sampled per taxon, every
numerical parameter of $\widetilde{\mathcal{N}}$ is identifiable from the quartet concordance factors
except the following, which are not:

1. the lengths of pendant edges;
2. for each $3$-cycle, the hybridization parameter and the lengths of the six edges in and adjacent to the
   cycle;
3. for each $4$-cycle, the hybridization parameter and the lengths of edges in the cycle and descended
   from its hybrid node, in the cases set out in the source's Proposition 29.

If at least two gene lineages are sampled in every taxon, which is modeled by attaching a cherry of two
pseudotaxa at each leaf, exceptions 1 and 3 disappear: all numerical parameters are then identifiable
except the hybridization parameters and the lengths of edges in and adjacent to $3$-cycles.

## Depends on

- [Two-cycles of a level-1 network are not identifiable from quartet CFs](level-1-two-cycles-not-identifiable.md)

## Proof depends on

- [Topological identifiability of a level-1 species network from quartet CFs](level-1-topological-identifiability-from-quartet-cfs.md)

## Expansion

With a single lineage per taxon no coalescent event can occur on a pendant edge, so pendant lengths never
enter the concordance-factor parameterization and cannot be recovered; attaching two pseudotaxa puts a
coalescence opportunity there and restores them. At a $3$-cycle the map from the seven numerical
parameters of the cycle and its adjacent edges into concordance factors factors through a six-dimensional
variety, so the parameters cannot all be identifiable, and eliminating all but one of them leaves only
the trivial relation that the three concordance factors of a quartet sum to $1$, so no single parameter is
identifiable either. Since a $2$-cycle is itself unidentifiable, the identifiable length of an edge that
replaced one is the effective length given by the $2$-cycle replacement identity.

## Sources

- E. S. Allman, H. Baños, M. Garrote-López and J. A. Rhodes, "Identifiability of level-1 species networks from gene tree quartets", Bulletin of Mathematical Biology 86 (2024), 110, <https://doi.org/10.1007/s11538-024-01339-4> (PMC11272829). (Theorem 30 and Corollary 31, with Propositions 20, 23 and 29.)
