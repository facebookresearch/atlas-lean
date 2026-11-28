# Replacement edges after deleting a spanning-forest edge

Let $F$ be a spanning forest of an undirected graph $G = (V, E)$ and let $e = \{u, v\} \in F$. Let $T_u$ and $T_v$ be the vertex sets of the two trees of $F - e$ containing $u$ and $v$. Then:

1. for $f \in E \setminus F$, the forest $F - e + f$ is a spanning forest of $G - e$ if and only if $f \in E_G(T_u, T_v)$;
2. if $E_G(T_u, T_v) \setminus \{e\} = \emptyset$, then $F - e$ is a spanning forest of $G - e$, and the component of $G$ containing $e$ splits into $T_u$ and $T_v$;
3. for every $e' \in E \setminus F$, the forest $F$ is a spanning forest of $G - e'$.

Hence connectivity queries reduce to tree queries in $F$, answered by Euler-tour trees or link-cut trees in $O(\log n)$ time per link, cut and query, and the whole difficulty of fully dynamic connectivity is to find a replacement edge in the cut $E_G(T_u, T_v)$.

## Proof sketch

Any spanning forest of $G - e$ restricted to the tree of $F$ containing $e$ must connect $T_u$ and $T_v$ if they are connected in $G - e$, and a single edge suffices exactly when it has one endpoint on each side. If no such edge exists, there is no path between $T_u$ and $T_v$ in $G - e$, since every such path leaves $T_u$ through an edge of the cut. Non-tree deletions do not affect $F$.

## Depends on

- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)
- [Spanning forest of an input graph](../../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/is-spanning-forest.md)

## Proof depends on

- [Connectivity via Euler tours](../link-cut-tree/connected-iff-tour.md)
- [Cutting an edge of a link-cut tree](../link-cut-tree/cut-edge.md)
- [Linking two trees of a link-cut tree state](../link-cut-tree/link.md)
- [Euler tour](../euler-tour-tree/tour.md)
- [Connectivity in a link-cut tree state](../link-cut-tree/connected.md)

## Sources

- Jacob Holm, Kristian de Lichtenberg, Mikkel Thorup, "Poly-logarithmic deterministic fully-dynamic algorithms for connectivity, minimum spanning tree, 2-edge, and biconnectivity", J. ACM 48(4) (2001).
- Bruce M. Kapron, Valerie King, Ben Mountjoy, "Dynamic graph connectivity in polylogarithmic worst case time", SODA (2013).
