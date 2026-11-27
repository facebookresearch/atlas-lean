# Hamiltonian cycle in a cubic bipartite three-connected planar graph

Every finite simple graph that is cubic, bipartite, planar, has at least four vertices, and remains connected after deleting any set of at most two vertices has a Hamiltonian cycle. Planarity means distinct plane vertex positions and injective continuous edges, with opposite parameterizations of the same edge related by reversal, no vertex contacts except designated endpoints, and disjoint interiors for distinct unordered edges. The conclusion is one closed spanning walk forming a cycle visiting each vertex exactly once, not merely a spanning 2-factor.

## Depends on

- Crossing-free topological drawing, deletion connectivity, cubic and bipartite simple graphs, and the Hamiltonian-cycle walk predicate.

## Expansion

Separate the exact-dual bridge: a connected finite simple graph with the stated plane embedding has a network realization and a finite exact dual on the same edge labels. Also separate the connectivity bridge: in a network on at least five vertices whose realization remains connected after at most two vertex deletions, every cut of a nonempty proper vertex set has at least three edges. The finite cubic bipartite graphs here meet the order condition.

Prove the matching theorem for a finite simple cubic network with that exact dual, three-edge connectivity, and a proper two-coloring of its vertices. For every prescribed edge there exists a perfect matching containing it whose edge complement, on the same vertex set, is connected. Establish this by induction across nontrivial three-edge cuts; the colored dual and its triangles enter in the case without such a cut. This matching theorem is separate from the final deduction that its connected spanning two-regular complement is a Hamiltonian cycle.

## Proof outline

Bridge the Arc/Walk model to the established native graph APIs, and formalize the reductions and cycle-lifting separately. Preserve connectivity after two deletions and distinguish an arbitrary 2-factor from a Hamiltonian one.

## Sources

- [Comparator statement: `OAI.Barnette.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BarnetteHamiltonian.lean#L48-L50)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/180.md)
- [Existence of the exact dual](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Hamiltonian/ExactDual.lean#L116-L121), [connectivity bridge](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean#L51-L58), [matching with connected complement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Hamiltonian/Gluing.lean#L294-L299), and [the resulting Hamiltonian cycle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Hamiltonian/Main.lean#L13-L31).
