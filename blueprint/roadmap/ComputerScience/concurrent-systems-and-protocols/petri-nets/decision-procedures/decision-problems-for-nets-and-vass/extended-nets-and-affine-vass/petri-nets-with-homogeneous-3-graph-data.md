# Petri nets with homogeneous 3-graph data: well quasi-order or undecidability

Petri nets with data carry tokens labeled by elements of a fixed relational structure. For data from a strongly homogeneous 3-graph, either the structure admits a well quasi-order, making the standard problems decidable, or all of them, from coverability to termination and boundedness, are undecidable.

**Setting (Lasota and Piórkowski).** Fix a countably infinite relational structure $\mathbb{A}$ over a finite vocabulary with equality, the *data domain*. A *Petri net with data* $\mathbb{A}$ has finite disjoint sets of places $P$ and transitions $T$ and arcs $A \subseteq P \times T \cup T \times P$; arcs are labeled by pairwise disjoint finite nonempty sets of variables, and each transition by a first-order formula over the vocabulary of $\mathbb{A}$ whose free variables label arcs incident to it. A configuration is a finite multiset over $P \times \mathbb{A}$; a transition fires under a valuation of its variables satisfying its formula in $\mathbb{A}$, removing the tokens named by its input arcs and adding those named by its output arcs. The *standard problems* include termination, place non-emptiness (equivalently coverability), boundedness and inevitability, for a given net and initial configuration. $\mathbb{A}$ is *homogeneous* if every isomorphism between finite induced substructures extends to an automorphism, and *strongly homogeneous* if moreover its finite substructures have the strong amalgamation property. $\mathbb{A}$ *admits wqo* if for every well quasi-order $X$ the finite induced substructures of $\mathbb{A}$ labeled by $X$, ordered by label-increasing embedding, form a well quasi-order. A *3-graph* $(V, C_1, C_2, C_3)$ has three irreflexive symmetric binary relations such that every pair of distinct elements lies in exactly one of them.

**Theorem (Lasota and Piórkowski).** A strongly homogeneous 3-graph $\mathbb{G}$ either admits wqo, or all standard problems are undecidable for Petri nets with data $\mathbb{G}$.

When an effective homogeneous structure admits wqo, all standard problems are decidable by the theory of well-structured transition systems, so the theorem confirms, for strongly homogeneous 3-graphs, Lasota's wqo dichotomy conjecture between decidability and undecidability. For homogeneous graphs the dichotomy follows from the known classification of homogeneous graphs.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The core result of the paper is that a strongly homogeneous 3-graph which does not admit wqo contains, for some $i, j$, arbitrarily long induced paths in the graph $(V, C_i \cup C_j)$. Such paths let a Petri net with data $\mathbb{G}$ simulate a deterministic two-counter machine started at zero: a counter value $n$ is stored as $n + 2$ tokens carrying the nodes of an induced path, a zero test checks that the two ends are adjacent, a decrement replaces an end by its neighbor on the path, and an increment extends the path by a nondeterministically guessed node. The halting place is then markable exactly when the machine halts. By homogeneity and König's lemma the graph also contains an infinite induced path, so the net terminates exactly when the machine halts, which gives the remaining problems. A good expansion links a page for the classification step, that a strongly homogeneous 3-graph either admits wqo or contains arbitrarily long induced paths in the union of two of its colors.

## Sources

- Sławomir Lasota and Radosław Piórkowski, *WQO dichotomy for 3-graphs*, Information and Computation 275 (2020), article 104541, https://doi.org/10.1016/j.ic.2020.104541; the main theorem, the core theorem and the reduction from two-counter machines, read in arXiv:1802.07612v3.
