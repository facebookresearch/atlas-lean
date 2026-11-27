# Determinacy of regular path queries is undecidable

No algorithm decides, given finitely many regular path queries (views) and another regular path query over the same alphabet, whether the views determine the query on edge-labeled graphs. Both the finite and the unrestricted versions are co-r.e.-hard; the finite version is co-r.e.-complete.

**Setting (Głuch, Marcinkowski and Ostropolski-Nalewaja).** Structures are directed graphs whose edges carry labels from a finite alphabet $\Sigma$ (relational structures with binary predicates from $\Sigma$). For a regular language $Q \subseteq \Sigma^\ast$, the *regular path query* $Q$ returns on a structure $\mathbb{D}$ the set $Q(\mathbb{D})$ of pairs $(x, y)$ of vertices joined by a directed path whose label word belongs to $Q$. A finite set $\mathcal{Q}$ of regular path queries *determines* a regular path query $Q_0$ if any two structures $\mathbb{D}_1, \mathbb{D}_2$ with $Q(\mathbb{D}_1) = Q(\mathbb{D}_2)$ for all $Q \in \mathcal{Q}$ satisfy $Q_0(\mathbb{D}_1) = Q_0(\mathbb{D}_2)$; in the *finite* version the structures range over finite graphs, in the *unrestricted* version over all graphs. The input gives the regular languages, for instance by finite automata.

**Theorem (Głuch, Marcinkowski and Ostropolski-Nalewaja).** The query determinacy problem for regular path queries is undecidable, in both the finite and the unrestricted version: both are co-r.e.-hard. Finite non-determinacy is recursively enumerable, so the finite version is co-r.e.-complete.

Undecidability had previously been known only when $Q_0$ may be context-free. Determinacy is decidable when every language consists of a single word (path queries, a result of Afrati), and it differs from the stronger notions of monotone determinacy and rewritability, which are decidable for regular path queries.

## Depends on

- [Graph databases and regular path queries](../datalog/graph-databases-and-regular-path-queries.md)
- [Determinacy of a query by views](determinacy-of-a-query-by-views.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction starts from a grid tiling problem: given a set of shades (including black) and a set of forbidden pairs of shaded edges, is there a square grid of some size whose horizontal and vertical edges carry shades, whose bottom-left vertical edge and upper-right horizontal edge are black, and which contains no forbidden path of length $2$. This problem is undecidable by a standard encoding of Turing machine computations. From an instance the proof builds regular path queries $\mathcal{Q}$ and $Q_0$ so that non-determinacy is witnessed by a structure built from red and green copies of the query paths (the "escape" from a red chain), which exists exactly when a correct grid exists. Accepting machines yield negative instances and non-accepting machines positive ones, which gives co-r.e.-hardness for both versions.

## Sources

- Grzegorz Głuch, Jerzy Marcinkowski and Piotr Ostropolski-Nalewaja, "Can One Escape Red Chains? Regular Path Queries Determinacy is Undecidable", Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2018), pp. 492–501, 2018, <https://doi.org/10.1145/3209108.3209120>; Theorem I.1 with the remark that follows it (co-r.e.-hardness of both versions), Section II, "Preliminaries" (structures and regular path queries), and Section IV, "The Reduction" (the tiling problem and the reduction), whose correctness is proved in Sections V to X of arXiv:1802.01554v1, read at <https://arxiv.org/abs/1802.01554v1>.
