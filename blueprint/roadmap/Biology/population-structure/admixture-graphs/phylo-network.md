# Phylo Network

An **age-monotone parent-bounded routing network**: an admixture graph (rooted, acyclic,
every non-root node with one parent (a tree node) or two parents (a reticulation node),
proportions normalized at every non-root node) equipped with node ages. This is the routing
skeleton of a rooted phylogenetic network with inheritance probabilities
(Yu–Degnan–Nakhleh 2012; Zhang–Ogilvie–Drummond–Stadler 2018), without the binary
out-degree classification, leaf labels, or strict temporal constraints of the fully binary
notion; out-degrees are unrestricted. Node ages `time` (measured backward from the present)
are only weakly monotone along edges: a parent is never younger than its child
(`time v ≤ time u`, so zero-length edges are allowed; constant ages are not excluded), and
the branch length of an edge `u → v` is `time u - time v`. This is strictly weaker than time
consistency in the phylogenetic sense, which would in addition force tree edges to advance
strictly in time. A lineage at `v` traces back to the parent `u` with probability
`inherit v u = prop v u`: this vanishes off the parents and sums to `1` over the parents, so
it is `1` at a tree node and `γ, 1 - γ` at a reticulation node.
