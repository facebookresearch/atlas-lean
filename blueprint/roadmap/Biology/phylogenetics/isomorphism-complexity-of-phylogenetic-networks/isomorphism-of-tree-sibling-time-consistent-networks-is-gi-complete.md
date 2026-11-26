# Isomorphism of tree-sibling time-consistent networks is GI-complete

**Definitions.** A rooted DAG (rDAG) has leaves (out-degree $0$), tree nodes (in-degree $\le 1$), hybrid nodes (in-degree $> 1$), and elementary nodes (tree nodes of out-degree $1$). For a finite label set $S$, an $S$-rDAG is an rDAG with leaves injectively labelled by $S$; isomorphisms must match equal labels. A **phylogenetic network on $S$** is an $S$-rDAG in which no tree node is elementary and every hybrid node has out-degree $1$ with a tree-node child. It is **tree-sibling** if every hybrid node has a sibling that is a tree node. A **temporal assignment** is a map $\tau : V \to \mathbb{N}$ with $\tau(u) = \tau(v)$ for every arc $(u,v)$ into a hybrid node and $\tau(u) < \tau(v)$ for every arc $(u,v)$ into a tree node; the network is **time-consistent** if one exists. Tree-sibling time-consistent networks are abbreviated TSTC.

A decision problem is **graph isomorphism-complete** (GI-complete) if it is polynomial-time equivalent to the isomorphism problem for finite graphs.

**Proposition 1 (cycle test for time consistency).** Let $E_H$ be the hybridization arcs of a phylogenetic network $N = (V, E)$ and $N^*$ the digraph on $V$ with arcs $E \cup \{(v,u) : (u,v) \in E_H\}$. Then $N$ is time-consistent iff $N^*$ has no cycle containing a tree arc of $N$.

**Proposition 2.** For every nonempty $S$, isomorphism of $S$-rDAGs is GI-complete.

**Theorem 3.** For every label set $S$ with $|S| \ge 3$, isomorphism of TSTC networks on $S$ is GI-complete.

**Proposition 4.** Up to relabelling, the only TSTC networks with fewer than three leaves are the one-node network and the tree with two leaves; so the bound $|S| \ge 3$ in Theorem 3 cannot be lowered.

**Corollary 5.** For $|S| \ge 3$, isomorphism of TSTC networks with leaves *bijectively* labelled by $S$ is GI-complete.

## Expansion

Proposition 2: an injectively labelled rDAG reduces to an unlabelled one by replacing label $k$ with $k$ fresh leaf children; conversely an unlabelled rDAG becomes an $S$-rDAG by adding one new leaf labelled $1$ below every old leaf. Both blow-ups are polynomial and isomorphism-preserving, and rDAG isomorphism is itself GI-complete.

Theorem 3 reduces $S$-rDAG isomorphism, with $S = \{1,\dots,n\}$, to TSTC isomorphism on $S \cup \{n+1, n+2\}$ (TSTC networks are a special case of $S$-rDAGs, giving the other direction). Starting from an $S$-rDAG $N$ that is not already a tree, (1) give every hybrid node a single new tree child that takes over its children; (2) subdivide every hybridization arc by a new node; (3) give every elementary node a new tree child $v'$; (4) subdivide the arc into the largest occurring label $m$ by a node $w_m$; (5) add two new nodes $a, b$ with arcs from every $v'$ and from $w_m$, so $a, b$ are hybrid; (6) hang new leaves $n+1$ under $a$ and $n+2$ under $b$. The result has no elementary nodes, every hybrid node now has a tree sibling (the child $v'$ of the subdivision node on any incoming arc, or $w_m$'s leaf $m$ for $a$ and $b$), and Proposition 1 shows time consistency. The construction is invertible in polynomial time, so $N_1 \cong N_2$ iff $\bar N_1 \cong \bar N_2$.

Consequence: semibinary TSTC networks (all hybrid in-degrees $2$) admit polynomial-time metrics separating non-isomorphic networks, for example the $\mu$-distance, but a polynomial-time metric with the separation property on *all* TSTC networks would place graph isomorphism in P.

## Sources

- G. Cardona, M. Llabrés, F. Rosselló, G. Valiente, "The comparison of tree-sibling time consistent phylogenetic networks is graph isomorphism-complete", The Scientific World Journal 2014 (2014) 254279, Propositions 1, 2, 4, Theorem 3 and Corollary 5, <https://doi.org/10.1155/2014/254279>, PMCID PMC3996867.
