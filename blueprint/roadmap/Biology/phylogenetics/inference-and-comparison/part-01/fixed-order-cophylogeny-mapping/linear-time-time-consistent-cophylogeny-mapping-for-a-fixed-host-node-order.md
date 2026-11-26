# Linear-time time-consistent cophylogeny mapping for a fixed host node order

Let $H$ be a rooted binary host tree with $m$ nodes whose internal nodes carry a fixed total order (a ranking of divergence times), let $P$ be a rooted binary parasite tree, and let $\phi$ map the parasite leaves to host leaves. A cophylogeny mapping $\Phi$ extends $\phi$ to all of $P$ using the events codivergence, duplication, host switch and loss; it is time-consistent if no host switch connects host edges that do not coexist in the same time interval of the order. A cherry is a pair of leaves with a common parent.

The local pattern-detection and collapse procedure processes host cherries in the order of the host node ranking (deepest first), detects at each cherry the parasite pattern it supports among a constant-size set of local patterns, records the corresponding event and collapses the cherry into its parent. Then:

1. Every host switch it records connects edges in the same time interval, so every reported mapping is time-consistent.
2. With $n = k + m$, where $k$ is the cost of mapping the parasite tree, the ordered list of current and future cherries can be built in $O(m)$ time, all patterns can be detected and collapsed in $O(k + m)$ time, and a post-processing step that relocates each host switch to take-off and landing edges in the same time interval minimizing the number of induced losses (using constant-time level-ancestor queries) also runs in $O(k + m)$ time.

Hence a time-consistent mapping for one fixed host order is computed in $O(n)$ time and space. Since minimum-cost cophylogeny reconstruction is NP-hard in general, the full problem is approached by searching over host node orders with a metaheuristic and calling this linear-time step for each order.

## Expansion

Time inconsistency would require a cherry forming a switch pattern with a host node that is younger than the cherry's parent; processing cherries in decreasing depth of their parents rules this out, which is a proof by contradiction. The cherry list is produced by computing root distances in one traversal and bucket-sorting by depth. Each parasite cherry consumes at least three nodes and reuses one, which bounds the total number of patterns by $O(k)$.

## Sources

- B. Drinkwater and M. A. Charleston, "Introducing TreeCollapse: a novel greedy algorithm to solve the cophylogeny reconstruction problem", BMC Bioinformatics 15 (Suppl. 16) (2014) S14, <https://doi.org/10.1186/1471-2105-15-S16-S14>, PMCID PMC4290644. Definitions 1–2, Lemmas 1–4, Theorems 1–2 and Corollary 1.
