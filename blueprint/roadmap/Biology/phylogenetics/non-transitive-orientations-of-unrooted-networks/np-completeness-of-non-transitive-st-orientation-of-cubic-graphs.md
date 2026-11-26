# NP-completeness of non-transitive st-orientation of cubic graphs

**Setting.** For an undirected graph $G=(V,E)$, an *orientation* assigns a direction to every edge. An arc $(u,v)$ of a digraph is *transitive* if there is a directed path from $u$ to $v$ not using $(u,v)$, and an orientation is *non-transitive* if it has no transitive arc. For $s,t\in V$, an *$st$-orientation* is an acyclic orientation in which $s$ is the unique source and $t$ the unique sink. The decision problem NT-st-Orientation asks, given $G$ and $s,t$, whether $G$ has a non-transitive $st$-orientation.

**Statement.**

1. NT-st-Orientation is NP-complete on cubic graphs (every vertex of degree exactly $3$).
2. It remains NP-complete on graphs in which $s$ and $t$ have degree $1$ and every other vertex has degree $3$.
3. The relaxed version, which asks whether a cubic graph has a non-transitive $st$-orientation for some choice of $s,t\in V$, is also NP-complete.

By contrast, deciding whether some $st$-orientation exists (without the non-transitivity requirement) is solvable in polynomial time.

## Expansion

Membership in NP is direct: given an orientation, the unique source and sink, acyclicity, and the absence of a bypassing path for each arc are checked by depth-first search. Hardness is a Karp reduction from a restricted Not-All-Equal 3-SAT in which every literal is a positive variable and every variable occurs exactly four times. The construction uses a new *fork gadget* with only degree-$1$ and degree-$3$ vertices that, in any non-transitive $st$-orientation, links the directions of three designated edges, together with source, sink and variable gadgets built from fork copies. A truth assignment corresponds to the orientation of variable edges, and a clause is nae-satisfied exactly when the corresponding gadget admits an orientation without transitive arcs. Degree-$2$ vertices created during the construction can be suppressed without changing the existence of a non-transitive orientation, which yields a cubic graph.

## Sources

- Janosch Döcker, Simone Linz, "Orientations without transitive arcs for cubic graphs and phylogenetic networks", arXiv:2608.28654 (2026), Theorem 4.6 and Corollary 4.7, <https://doi.org/10.48550/arXiv.2608.28654>
