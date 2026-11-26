# Absence of infinite critical clusters on quasi-transitive bond graphs

Take an infinite vertex set and labelled unoriented bonds (loops and parallel bonds are allowed). Assume the underlying connectivity graph is connected, only finitely many bonds touch each vertex, and the group of vertex and bond relabellings preserving incidence has finitely many vertex orbits. Retain each labelled bond independently with probability $p\in[0,1]$. Reachability by a finite open path, including paths of length zero, gives the clusters, and loops can be discarded for connectivity. Define $p_c$ as the infimum of the parameters at which the probability that some infinite cluster exists is positive. If $p_c<1$, that probability is zero under the law at $p_c$.

**Conventions.** Use the labelled independent bond law, incidence-preserving quasi-transitivity and the existence-event definition of $p_c$. The simple-graph [critical-probability model](../percolation-probability-and-critical-point/README.md) uses distinct unordered edges; any reduction to it must account for the parallel-bond probabilities.

## Depends on

- [Independent bonds with separate edge labels](labelled-independent-bond-law.md)

## Proof depends on

The critical exclusion argument for quasi-transitive locally finite bond graphs with $p_c<1$, including the finite-scale construction that would turn critical percolation into percolation at a smaller parameter. Continuity from above at $p_c$ alone does not show the required value at $p_c$.

## Expansion

Develop the labelled-bond product law and measurable component events, then decompose the finite-scale exclusion proof into its crossing, separation and sprinkling ingredients. Do not replace incidence-preserving automorphisms by arbitrary underlying simple-graph automorphisms.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalPercolation.lean#L50-L59)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/213.md)
- [Accompanying manuscript: No percolation at criticality on quasi-transitive graphs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf)
- [Background: Benjamini and Schramm, Percolation beyond Z^d, many questions and a few answers](https://doi.org/10.1214/ecp.v1-960)
