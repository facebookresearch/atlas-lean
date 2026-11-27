# Implication of regular graph constraints over heaps is undecidable

Whether every heap satisfying one regular graph constraint also satisfies another is undecidable, although satisfiability over heaps and implication over arbitrary graphs are decidable.

**Theorem.** The implication problem for [regular graph constraints](regular-graph-constraints-over-heaps.md) over the class of heaps is undecidable: no algorithm decides, given finite graphs $G_1$ and $G_2$, whether every heap $H$ with $H \to G_1$ also satisfies $H \to G_2$. (The set of pairs for which implication fails is recursively enumerable, so implication is co-recognizable.)

## Depends on

- [Regular graph constraints over heaps](regular-graph-constraints-over-heaps.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof has two steps. First the source introduces *corresponder graphs*, heaps $\mathrm{CG}(n, k, u_1, \dots, u_{k-1}, l_1, \dots, l_{k-1})$ made of three $s_1$-chains of $2k$, $2n$ and $2n$ nodes linked by further edges, whose parameters mimic solutions of Post correspondence problem instances. Satisfiability of a constraint by some corresponder graph is undecidable, by a reduction from PCP. Second, corresponder graphs are characterized among heaps by the presence of a homomorphism to one fixed graph together with the absence of homomorphisms to finitely many fixed graphs. For a given constraint $G$, a heap is a counterexample to the implication $(G \times P) \Rightarrow Q$, with $\times$ the product of graphs (which expresses conjunction) and $P$, $Q$ the fixed characterizing graphs, exactly when it is a corresponder graph satisfying $G$. Since implication fails exactly when some heap is a counterexample, and heaps can be enumerated and checked, implication is co-recognizable.

The source draws the consequence that procedure preconditions or data-structure invariants expressed in any specification language at least as expressive as regular graph constraints cannot be checked algorithmically. Its abstract presents the result as a contrast to existential monadic second-order logic, which is strictly more expressive.

## Sources

- Viktor Kuncak and Martin Rinard, "Existential Heap Abstraction Entailment Is Undecidable", in *Static Analysis (SAS 2003)*, Lecture Notes in Computer Science 2694, Springer, 2003, pp. 418–438, <https://doi.org/10.1007/3-540-44898-5_24>; read as the technical report arXiv:cs/0408014v1, "Typestate Checking and Regular Graph Constraints", <https://arxiv.org/abs/cs/0408014v1>: Theorem 38 in Section 3.4 ("The Undecidability Result") of Section 3 ("Undecidability of Implication"), in the numbering of that version.
