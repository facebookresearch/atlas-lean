# Strong thin spanning trees in multigraphs

There exists an absolute $C>0$ such that for every integer $k\ge1$ and every finite loopless multigraph on at least two vertices with at least $k$ edges across every nonempty proper cut, there is a spanning tree $T$ satisfying $|T\cap\delta(S)|\le (C/k)|\delta(S)|$ for every nonempty proper cut $S$. Edges are distinguished even when parallel; a spanning tree is a connected spanning edge set made disconnected by removing any of its edges. Connectedness means every nontrivial cut has a selected edge.

## Depends on

- Labelled loopless multigraph cuts and trees defined by minimally cut-connected sets.

## Expansion

Separate the packing thinness theorem on a finite labelled multigraph with r≥1 disjoint spanning trees: one spanning tree has every nontrivial cut count at most C/r times the ambient cut count, with one absolute C. The graph's edge-connectivity-to-packing conversion and r=0 boundary are distinct from that theorem.

## Proof outline

Define the edge-labelled cut bridge and separate the uniform thinning estimate from the tree extraction. Verify the cut condition on two vertices with parallel edges; multiplicities cannot be discarded.

## Sources

- [Comparator statement: `OAI.StrongThinTree.strongThinTree`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StrongThinTree.lean#L38-L40)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/174.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ThinTrees/Main.lean)
