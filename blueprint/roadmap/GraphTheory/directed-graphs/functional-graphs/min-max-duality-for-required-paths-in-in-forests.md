# Min-max duality for required paths in in-forests

Let $\alpha$ be finite with a partial successor map $\sigma$ whose graph has no cycles (an in-forest), and let $r : \alpha \to \mathbb{N}$ be a requirement. A directed path along $\sigma$ is required if it is nonempty and its number of vertices is at least $r(v)$ at its final vertex $v$. For every finite $S \subseteq \alpha$, the minimum size of a set $H \subseteq S$ meeting every required path inside $S$ equals the maximum number of pairwise vertex-disjoint required paths inside $S$. Moreover, finite functional forests admit interval labels $\mathrm{low}, \mathrm{high} : \alpha \to \{0, \dots, |\alpha| - 1\}$ such that $y$ is reached from $x$ before cycle entry iff $\mathrm{low}(y) \le \mathrm{low}(x) \le \mathrm{high}(y)$.

## Proof sketch

Weak duality is immediate, since a hitting set must meet each path of a disjoint packing in a distinct vertex. For equality, process vertices from the leaves toward the roots and take the greedy path ending as early as possible above each unhit subtree; its final vertex joins $H$, and the chosen paths are disjoint. The interval labels come from ranking root-to-vertex paths lexicographically, where the extensions of a prefix form an interval.

## Depends on

- [Functional graphs: transient depth, cycles and canonical cycle representatives](functional-graph-transient-depth-and-cycles.md)

## Sources

- S. Schlesinger, "Square-root circuit bounds for iterated functions", 2026.
