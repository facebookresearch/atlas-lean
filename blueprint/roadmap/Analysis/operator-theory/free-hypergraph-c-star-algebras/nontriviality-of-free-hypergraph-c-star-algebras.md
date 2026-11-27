# Whether a free hypergraph C*-algebra is zero is undecidable

No algorithm decides, given a finite hypergraph, whether its free hypergraph C*-algebra is zero, that is, whether the hypergraph has a quantum representation by closed subspaces of some nonzero Hilbert space; this is the inverse sandwich conjecture.

**Theorem (Fritz).** There is no algorithm to determine, for a given finite hypergraph $H$, whether $C^*(H) = 0$.

The problem remains undecidable when every edge of $H$ has at most $3$ vertices. It is semi-decidable, so it has the Turing degree of the halting problem. Its commutative analogue, whether some assignment of truth values to the vertices makes exactly one vertex true in each edge, is the NP-complete problem 1-in-3-SAT.

## Depends on

- [Free hypergraph C*-algebras](free-hypergraph-c-star-algebra.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The proof uses "Existence of a perfect commuting-operator strategy for a linear system game is undecidable", which has no page on main yet; link it once its page lands.

The proof, in Fritz's paper on quantum logic, reduces from Slofstra's theorem that for linear systems over $\mathbb Z_2$ it is undecidable whether $J = 1$ in the solution group; a quantum solution of the linear system becomes a quantum representation of a hypergraph. Slofstra's theorem is linked above in its equivalent form for perfect commuting-operator strategies of linear system games. The restriction to edges of size at most $3$ uses that every free hypergraph C\*-algebra is computably isomorphic to one whose edges all have $3$ vertices (Lemma 2.15 of the source), and semi-decidability comes from the operator-norm algorithms of Fritz, Netzer and Thom, which have no page yet; a good expansion links pages for them and for the translation from linear systems to hypergraphs.

## Sources

- Tobias Fritz, "Quantum logic is undecidable", *Archive for Mathematical Logic* 60(3–4), 2021, pp. 329–341, <https://doi.org/10.1007/s00153-020-00749-0>: Corollary 11 (cited after the paper below, which restates it).
- Tobias Fritz, "Curious properties of free hypergraph C*-algebras", *Journal of Operator Theory* 83(2), 2020, pp. 423–445, <https://doi.org/10.7900/jot.2018oct18.2240>; read as arXiv:1808.09220v3, <https://arxiv.org/abs/1808.09220v3>: Theorem 3.1, the paragraph after it, Remark 3.2 and Remark 3.3, in the paragraph "Nontriviality" of Section 3 of that version.
