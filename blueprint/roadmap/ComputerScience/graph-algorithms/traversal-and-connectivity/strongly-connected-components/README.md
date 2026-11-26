# Strongly connected components

The components can be computed from depth-first search alone. Number the vertices in the order
the search reaches them; each component forms a subtree of the depth-first spanning forest, and
a vertex is the root of its component exactly when its LOWLINK is itself (Tarjan, SIAM J. Comput.
1(2) (1972), §4). That test is the basis of Tarjan's linear-time algorithm. The
[strongly connected components algorithm](components.md) of this topic is simpler and slower: it
tests mutual reachability of pairs of vertices directly, with two depth-first searches per pair.

- [Strongly connected vertices](strongly-connected.md)
- [Strong connectivity is reflexive](strongly-connected-refl.md)
- [Strong connectivity is symmetric](symm.md)
- [Strong connectivity is transitive](trans.md)
- [Strong connectivity as an equivalence relation](strongly-connected-setoid.md)
- [Executable mutual-reachability test](same-component-b.md)
- [The mutual-reachability test is correct](same-component-b-eq-true.md)
- [Strongly connected components algorithm](components.md)
- [Computed components are nonempty](components-nonempty.md)
- [Computed components have no repeated vertices](components-nodup.md)
- [Computed components are pairwise disjoint](components-pairwise-disjoint.md)
- [The computed components cover the vertex list](mem-flatten-components.md)
- [Vertices share a computed component exactly when strongly connected](share-component-iff-strongly-connected.md)
- [Each computed component is a full mutual-reachability class](component-maximal.md)
- [SCC partition](is-sccpartition.md)
- [The computed components form the SCC partition](components-is-sccpartition.md)
- [Reachability between components](component-reaches.md)
- [Acyclic condensation](condensation-acyclic.md)
- [The condensation of the computed components is acyclic](components-condensation-acyclic.md)
- [Ancestor in a depth-first spanning forest](tree-ancestor.md)
- [Reversing the parent list preserves tree ancestry](tree-ancestor-reverse.md)
- [Numbering properties of depth-first search](is-dfsnumbering.md)
- [First vertex of a strongly connected component](is-first-in-component.md)
- [$\mathrm{LOWLINK}(v) = v$](lowlink-eq-self.md)
- [Strongly connected components are closed under tree paths](strongly-connected-of-tree-ancestor-betw.md)
- [The first vertex of a component is an ancestor of all of it](tree-ancestor-of-first.md)
- [Common ancestor of strongly connected vertices](exists-common-ancestor-strongly-connecte.md)
- [The highest-numbered common ancestor lies in the component](strongly-connected-of-highest-common-anc.md)
- [Tarjan's lowlink test for component roots](is-first-in-component-iff-lowlink-eq-sel.md)
- [Tree arcs of depth-first search of the whole graph are edges](dfs-all-parent-edge.md)
- [Ancestors are discovered first in depth-first search of the whole graph](dfs-all-num-le-of-tree-ancestor.md)
- [Descendants are numbered consecutively in depth-first search](dfs-all-tree-ancestor-of-between.md)
- [Edges of a depth-first search go to descendants or to earlier vertices](dfs-all-edge-cases.md)
- [Depth-first search of the whole graph has the depth-first numbering properties](dfs-all-is-dfsnumbering.md)
- [Strongly connected vertices have a common ancestor in their component (depth-first search)](dfs-all-exists-common-ancestor-strongly.md)
- [Tarjan's lowlink test for depth-first search of the whole graph](dfs-all-is-first-in-component-iff-lowlin.md)

## Related topics

- [Depth-first search](../depth-first-search/README.md): the search whose numbering properties
  the lowlink test uses.
- [Topological sorting](../topological-sorting/README.md): the components form an acyclic
  condensation, which can be sorted topologically.
