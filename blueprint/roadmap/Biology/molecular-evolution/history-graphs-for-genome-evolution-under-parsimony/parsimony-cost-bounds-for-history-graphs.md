# Parsimony cost bounds for history graphs

**Setting.** A *thread graph* has vertices (DNA bases, each with two sides), optional base labels, and undirected *adjacencies* between sides. A *history graph* $G$ adds directed *branches* from ancestral to descendant vertices, each vertex having at most one incoming branch, such that contracting the adjacencies leaves a directed acyclic *event graph*. A *simple history* is a fully specified history graph: every vertex is labelled, and the genome is organised into *epochs* separated by replications, with labels changing only by substitutions and adjacencies only by DCJ rearrangements. A *realisation* of $G$ is a simple history obtained from $G$ by adding elements (an *extension*) and, for a *cost function* $c(s, r)$, meaning a monotone function of the substitution count $s$ and rearrangement count $r$ in which both substitutions and rearrangements have positive cost ($c(s+1,r)>c(s,r)$ and $c(s,r+1)>c(s,r)$), the cost $C(G, c)$ is the minimum of $c(s(H), r(H))$ over realisations $H$.

- *Lemma 1.* The rearrangement cost of an epoch of a simple history equals the minimum number of DCJ operations converting the root layer's adjacencies into the leaf layer's adjacencies.
- *Lemma 4.* Computing $C(G, c)$ is NP-hard (it contains NP-hard small-parsimony problems for substitutions or rearrangements alone).

**Ambiguity and AVGs.** Labels and adjacencies of $G$ are *lifted* to their nearest labelled (respectively attached) ancestors. The substitution ambiguity $u_s(G)$ counts non-trivial lifted labels in excess of one per vertex, the rearrangement ambiguity $u_r(G)$ counts non-trivial lifted adjacency incidences in excess of one per side, and $G$ is an *ancestral variation graph* (AVG) if $u_s(G) + u_r(G) = 0$. Simple histories are AVGs.

**Bounds.** Let $s_l(G)$ (lower-bound substitution cost) be the number of distinct non-trivial lifted labels over all vertices minus the number of unlabelled vertices carrying non-trivial lifted labels, and $s_u(G)$ the total number of non-trivial lifted labels minus, at each such unlabelled vertex, the maximum multiplicity of an identical lifted label. Group the sides carrying real or lifted adjacencies into connected *modules* $M$ of the module graph and set

$$r_l(G) = \sum_{M} \left(\left\lceil \tfrac{|V_M|}{2} \right\rceil - 1\right),$$

with $r_u(G)$ the corresponding upper bound.

**Theorem 1.** For every history graph $G$ and every cost function $c$,

$$c\big(s_l(G), r_l(G)\big) \;\le\; C(G, c) \;\le\; c\big(s_u(G), r_u(G)\big),$$

with equality throughout when $G$ is an AVG (then $s_l = s_u$ and $r_l = r_u$).

**Theorems 2–4 (finite search space).** An element of an extension $G'$ of $G$ is *$G$-reducible* if some reduction sequence from $G'$ back to $G$ deletes (or, for a branch, contracts) it, and the *$G$-unbridged graph* of $G'$ deletes all $G$-reducible bridge adjacencies. Call $G'$ *$G$-bounded* if it contains no $G$-reducible non-minimal element and its $G$-unbridged graph contains no $G$-reducible ping adjacency (one of a pair of adjacencies with hanging sides that point back to each other through their nearest attached ancestors). An AVG extension of $G$ is *$G$-optimal* for $c$ if it attains $C(G,c)$ and has no proper reduction that is still an AVG extension of $G$. The $G$-bounded AVGs contain all $G$-optimal AVGs for every cost function. This uses the positive costs: the source excludes $G$-reducible ping adjacencies by deleting one and repairing the graph, which gives an AVG extension with one rearrangement fewer and the same substitutions, contradicting optimality only when a rearrangement has positive cost. The finiteness of the set of $G$-optimal AVGs, which contrasts with the existence of a $G$ with infinitely many $G$-minimal AVG extensions (Lemma 9 of the source), is derived from this containment and the size bounds below, so it too rests on the positive costs. If $G$ has $n$ adjacencies and $m$ labelled vertices, a $G$-bounded history graph has at most $\max(0, 10n-8)$ $G$-reducible adjacencies and at most $\max(0, 2m-2, 20n-16, 20n+2m-18)$ additional vertices, and these bounds are tight. Consequently the $G$-bounded poset under reduction is finite, has $G$ as its unique least element, its maximal elements are AVGs, and its covering relation is a single bounded reduction operation, so the space of most-parsimonious interpretations can be explored by local moves.

## Depends on

- [Double-cut-and-join distance formula](../../bioinformatics/genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

In an AVG every vertex has at most one non-trivial lifted label and every side at most one non-trivial lifted adjacency, so each substitution or DCJ event is forced and the lower and upper counts coincide; Lemmas 17 and 21 of the source show that every history graph has an AVG extension and that every AVG has a realisation achieving its bounds, which yields Theorem 1. Within a module of $|V_M|$ sides that must be re-paired, each DCJ can resolve at most two sides, giving the $\lceil |V_M|/2 \rceil - 1$ count, analogous to the cycle-counting formula for DCJ distance. Theorem 3 follows by charging every reducible adjacency or label to incidences projected from the $n$ adjacencies and $m$ labels of $G$, which caps the size of any bounded extension linearly.

## Sources

- B. Paten, D. R. Zerbino, G. Hickey, D. Haussler, "A unifying model of genome evolution under parsimony", BMC Bioinformatics 15 (2014) 206, Lemmas 1, 4, 5, Theorems 1–4 and Methods, <https://doi.org/10.1186/1471-2105-15-206>, PMCID PMC4082375.
