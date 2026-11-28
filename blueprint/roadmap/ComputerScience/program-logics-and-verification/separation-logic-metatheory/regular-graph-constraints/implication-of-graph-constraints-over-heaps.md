# Implication of regular graph constraints over heaps is undecidable

Whether every heap satisfying one regular graph constraint also satisfies another is undecidable, although satisfiability over heaps and implication over arbitrary graphs are decidable.

**Theorem.** The implication problem for [regular graph constraints](regular-graph-constraints-over-heaps.md) over the class of heaps is undecidable: no algorithm decides, given finite graphs $G_1$ and $G_2$, whether every heap $H$ with $H \to G_1$ also satisfies $H \to G_2$.

## Depends on

- [Regular graph constraints over heaps](regular-graph-constraints-over-heaps.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof has two steps. First the source introduces *corresponder graphs*, heaps $\mathrm{CG}(n, k, u_1, \dots, u_{k-1}, l_1, \dots, l_{k-1})$ made of three $s_1$-chains of $2k$, $2n$ and $2n$ nodes linked by further edges, whose parameters mimic solutions of Post correspondence problem instances. Satisfiability of a constraint by some corresponder graph is undecidable, by a reduction from PCP. Second, corresponder graphs are characterized among heaps by the presence of a homomorphism to one fixed graph together with the absence of homomorphisms to finitely many fixed graphs. For a given constraint $G$, a heap is a counterexample to the implication $(G \times P) \Rightarrow Q$, with $\times$ the product of graphs (which expresses conjunction) and $P$, $Q$ the fixed characterizing graphs, exactly when it is a corresponder graph satisfying $G$. Implication is [co-recognizable](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md) by an elementary argument not stated in the source: implication fails exactly when some heap is a counterexample, heaps are finite graphs that can be enumerated, and whether a heap $H$ maps homomorphically to a finite graph can be decided by trying every map.

The SAS paper draws the consequence that there is no complete algorithm for statically checking procedure preconditions or postconditions expressed by regular graph constraints; the technical report states it for procedure preconditions or data-structure invariants in any specification language at least as expressive as regular graph constraints. The abstract of the technical report presents the result as a contrast to existential monadic second-order logic, which is strictly more expressive. A good expansion links pages for the two lemmas of this proof: the undecidability of satisfiability of a regular graph constraint by a corresponder graph, and the characterization of corresponder graphs by homomorphisms to finitely many fixed graphs.

## Sources

- Viktor Kuncak and Martin Rinard, "Existential Heap Abstraction Entailment Is Undecidable", in *Static Analysis (SAS 2003)*, Lecture Notes in Computer Science 2694, Springer, 2003, pp. 418–438, <https://doi.org/10.1007/3-540-44898-5_24>; read in the authors' copy at <http://people.csail.mit.edu/rinard/paper/sas03.pdf>: Definitions 1, 2 and 4–7 in Section 2 and Theorem 14 (implication over heaps), in its numbering. Also read: the earlier technical report, "Typestate Checking and Regular Graph Constraints", arXiv:cs/0408014v1, <https://arxiv.org/abs/cs/0408014v1>, where the result is Theorem 38 in Section 3.4.
