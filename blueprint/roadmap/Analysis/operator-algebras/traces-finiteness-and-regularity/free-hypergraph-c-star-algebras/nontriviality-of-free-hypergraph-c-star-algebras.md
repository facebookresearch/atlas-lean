# Whether a free hypergraph C*-algebra is zero is undecidable

No algorithm decides, given a finite hypergraph, whether its free hypergraph C*-algebra is zero, equivalently whether the hypergraph has no quantum representation on a nonzero Hilbert space; this is the inverse sandwich conjecture.

**Theorem (Fritz).** There is no algorithm to determine, for a given finite hypergraph $H$, whether $C^*(H) = 0$.

The algebra $C^*(H)$ is nonzero exactly when $H$ has a quantum representation on some nonzero Hilbert space. The problem remains undecidable when every edge of $H$ has at most $3$ vertices, a result of Atserias, Kolaitis and Severini. The set of $H$ with $C^*(H) = 0$ is semi-decidable, and the halting problem reduces to the problem (through the word problem for groups), so it has the [Turing degree](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-degree-of.md) of the [halting set](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-reducibility/halting-set.md). Its commutative analogue asks whether some set of vertices meets every edge in exactly one vertex; for finite hypergraphs it is a Boolean satisfiability problem, hence decidable, and it is [NP-complete](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md), by the NP-completeness of 1-in-3-SAT, as the source notes. As a problem on finite set systems it is the [exact hitting set problem](../../../../TheoryOfComputation/np-completeness/set-systems-and-location/exact-hitting-set/exact-hitting-set-np-complete.md).

## Depends on

- [Free hypergraph C*-algebras](free-hypergraph-c-star-algebra.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Turing degree of a predicate](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-degree-of.md)
- [Halting set](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-reducibility/halting-set.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

None.

## Expansion

The proof, in Fritz's paper on quantum logic, reduces from Slofstra's theorem that for linear systems over $\mathbb Z_2$ it is undecidable whether $J = 1$ in the solution group; a quantum solution of the linear system becomes a quantum representation of a hypergraph. The restriction to edges of size at most $3$ uses that every free hypergraph C\*-algebra is computably isomorphic to one whose edges all have $3$ vertices (Lemma 2.15 of the source), and semi-decidability comes from the operator-norm algorithms of Fritz, Netzer and Thom. Slofstra's theorem itself is undecidable by reduction from the word problem for groups, which is undecidable by reduction from the halting problem (the paragraph after Theorem 3.1 of the source).

A good expansion adds and links pages for Slofstra's theorem, in its form that perfect commuting-operator play of linear system games is undecidable, for the translation from linear systems to hypergraphs, for Lemma 2.15 of the source and for the operator-norm algorithms of Fritz, Netzer and Thom.

## Sources

- Tobias Fritz, "Quantum logic is undecidable", *Archive for Mathematical Logic* 60(3–4), 2021, pp. 329–341, <https://doi.org/10.1007/s00153-020-00749-0>: Corollary 11 (cited after the paper below, which restates it).
- Tobias Fritz, "Curious properties of free hypergraph C*-algebras", *Journal of Operator Theory* 83(2), 2020, pp. 423–445, <https://doi.org/10.7900/jot.2018oct18.2240>; read as arXiv:1808.09220v3, <https://arxiv.org/abs/1808.09220v3>: Theorem 3.1, the paragraph after it, Remark 3.2 and Remark 3.3, in the paragraph "Nontriviality" of Section 3 of that version.
- Albert Atserias, Phokion G. Kolaitis and Simone Severini, "Generalized satisfiability problems via operator assignments", in *Fundamentals of Computation Theory (FCT 2017)*, Lecture Notes in Computer Science 10472, Springer, 2017, pp. 56–68, <https://doi.org/10.1007/978-3-662-55751-8_6> (cited after the paper above, for the restriction to edges with at most 3 vertices).
