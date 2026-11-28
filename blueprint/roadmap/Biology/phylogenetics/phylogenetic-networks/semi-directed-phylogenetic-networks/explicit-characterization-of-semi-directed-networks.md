# Explicit characterization of semi-directed phylogenetic networks

**Setting.** Write $d(v)$ for the degree and $d^-(v)$ for the in-degree of a vertex. A rooted phylogenetic network is a directed acyclic graph with a single root (a vertex of in-degree $0$) whose leaves are labelled by taxa, such that $d(v)\ne2$ for every non-root vertex $v$ and $d^-(v)\in\{0,1,d(v)-1\}$ for every vertex $v$; reticulations are vertices of in-degree at least $2$, so a reticulation has exactly one outgoing arc. (Without these degree conditions the characterization fails: a vertex with in-degree and out-degree $2$ keeps two incoming arcs after semi-deorientation and violates condition 1.) Its *semi-deorientation* replaces every arc $(u,v)$ whose head has in-degree $1$ by an undirected edge $\{u,v\}$ and suppresses a root of degree $2$; only arcs into reticulations keep their direction. A *semi-directed network* is a mixed graph $G=(V,E,A)$ (edges $E$, arcs $A$) that is the semi-deorientation of some rooted phylogenetic network. In a cycle $(v_0,\dots,v_{p-1},v_0)$, a reticulation $v_i$ is a *sink* if both cycle arcs at $v_i$ point into it. A *$\wedge$-path* between $u$ and $v$ is a path $(u=v_1,\dots,v_p=v)$ such that, for some $i$, both $(v_i,\dots,v_1)$ and $(v_i,\dots,v_p)$ are semi-directed paths (traversing arcs only forwards).

**Theorem.** A mixed graph $G=(V,E,A)$ is a semi-directed network if and only if

1. $d(v)\ne 2$ and $d^-(v)\in\{0, d(v)-1\}$ for every $v\in V$;
2. every cycle of $G$ contains at least one sink; and
3. $G$ contains a $\wedge$-path between every pair of vertices.

Moreover, if $N=(V,E,A)$ is the semi-deorientation of a network with $k\ge 1$ roots, its reticulation number is $|E|+|A|-|V|+k$; for a semi-directed network ($k=1$) it is $|E|+|A|-|V|+1$.

## Expansion

Condition 1 says that each vertex is either a tree vertex (no incoming arcs) or a reticulation (all but one incident link are incoming arcs). Condition 2 excludes semi-directed cycles, so some orientation of the undirected edges is acyclic, and condition 3 forces a single source component in which a root can be placed so that every vertex is reachable. The reticulation-number formula is the cycle rank $|E|+|A|-|V|+1$ of the underlying graph, adjusted by the extra roots.

## Sources

- N. Holtgrefe, K. T. Huber, L. van Iersel, M. Jones, "Characterizing semi-directed phylogenetic networks and their multi-rootable variants", *Theory in Biosciences* 145(1) (2025), 4, Corollary 1 and Theorem 3, <https://doi.org/10.1007/s12064-025-00453-8> (preprint arXiv:2507.18772).
