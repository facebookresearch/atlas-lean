# Strong amplifiers from weighted graphs with self-loops

**Theorem (Pavlogiannis–Tkadlec–Chatterjee–Nowak).** Fix $\varepsilon > 0$ and $N_0 > 0$, and let $G_1, G_2, \dots$ be connected **undirected** unweighted graphs with self-loops, $G_N$ having $N$ vertices and diameter at most $N^{1-\varepsilon}$ for all $N > N_0$. Then there is an explicit assignment of nonnegative weights to the edges and self-loops of each $G_N$ such that the resulting weighted graphs form a strong amplifier for the birth–death Moran process under **both** uniform and temperature initialization (and hence under any mixture of the two): for every fixed $r > 1$,

$$\rho(G_N, r, \mathrm U) \to 1 \quad\text{and}\quad \rho(G_N, r, \mathrm T) \to 1 \qquad (N \to \infty).$$

The theorem is stated only for undirected graphs, whose edge set is symmetric ($i \to j$ is an edge exactly when $j \to i$ is; Supplementary Note 1, Theorem 5); the source proves nothing for directed topologies. Since an edge can be removed by giving it weight $0$, the result applies to sparse topologies such as stars, toroidal grids, sunflowers, wheels, concentric circles and trees.

## Depends on

- [Amplifiers, strong amplifiers and initialization schemes](amplifiers-strong-amplifiers-and-initialization-schemes.md)

## Proof sketch

The construction partitions the vertices into a **hub** and several **branches** attached to it, with the hub larger than every single branch but much smaller than all branches together, so the first mutant appears in a branch with high probability; the diameter bound is what makes such a partition possible. Weights are chosen so that (i) inside each branch every edge is used more often toward the hub than away from it, and self-loop weights make edges nearer the hub busier, creating a global flow toward the hub, and (ii) the hub is almost isothermal and evolves fast. Fixation then proceeds in three stages: the mutant lineage rides the flow to the hub-adjacent vertex; it seeds the hub repeatedly until, with a constant chance each time, mutants fix in the (nearly well-mixed) hub; finally the mutant hub resists resident reinvasion, whose success probability is of order $r^{-n}$ for a hub of size $n$, while mutants take over the branches one by one against the flow. Simulations show the weighted stars, grids and sunflowers already amplify strongly at moderate $N$, unlike their unweighted versions.

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee and M. A. Nowak, "Construction of arbitrarily strong amplifiers of natural selection using evolutionary graph theory", Communications Biology 1 (2018), article 71, Results ("Construction of strong amplifiers") and Methods ("Construction of strong amplifiers"); Supplementary Note 1, Section 5, Theorem 5 (for unweighted, undirected graphs; full proof in the companion preprint arXiv:1802.02509), <https://doi.org/10.1038/s42003-018-0078-7>, PMCID PMC6123726.
