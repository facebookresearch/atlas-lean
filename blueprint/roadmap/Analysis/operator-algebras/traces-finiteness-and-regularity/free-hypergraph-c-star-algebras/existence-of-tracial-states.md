# Existence of a tracial state on a free hypergraph C*-algebra is undecidable

No algorithm decides, given a finite hypergraph, whether its free hypergraph C*-algebra has a tracial state; the absence of a tracial state is semi-decidable, and the halting problem reduces to the problem, so it has the Turing degree of the halting problem.

**Theorem (Fritz).** There is no algorithm to determine, for a given finite hypergraph $H$, whether $C^*(H)$ has a tracial state.

A tracial state is a positive linear functional $\tau$ with $\tau(1) = 1$ and $\tau(ab) = \tau(ba)$ for all $a, b$. If $C^*(H)$ has no tracial state, a hierarchy of semidefinite programs of Klep and Povh detects this, so the complement of the problem is semi-decidable; since the halting problem reduces to the problem (through Slofstra's theorem for binary constraint systems), it has the [Turing degree](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-degree-of.md) of the [halting set](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-reducibility/halting-set.md).

## Depends on

- [Free hypergraph C*-algebras](free-hypergraph-c-star-algebra.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Turing degree of a predicate](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-degree-of.md)
- [Halting set](../../../../TheoryOfComputation/degrees-and-hierarchies/turing-reducibility/halting-set.md)

## Proof depends on

- [Perfect commuting strategies and the synchronous game algebra](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/perfect-strategies-and-synchronous-game-algebra.md)

## Expansion

Every C\*-algebra of a synchronous nonlocal game is, constructively, a free hypergraph C\*-algebra (Theorem 2.19 of the source), so it suffices to treat game algebras. Such an algebra has a tracial state exactly when the game has a perfect commuting-operator strategy (Helton, Meyer, Paulsen and Satriano, Theorem 3.2(3), linked above), and the synchronous games built from binary constraint systems (Kim, Paulsen and Schafhauser, Corollary 4.4(1)) reduce Slofstra's undecidability theorem for perfect commuting-operator strategies of binary constraint system games to the question. That theorem is in turn proved by reduction from the halting problem (proof of Corollary 3.7 of the source).

A good expansion adds and links pages for Slofstra's undecidability theorem for binary constraint system games, the hypergraph form of synchronous game algebras (Theorem 2.19 of the source), the synchronous games of binary constraint systems, and the semidefinite hierarchy of Klep and Povh.

## Sources

- Tobias Fritz, "Curious properties of free hypergraph C*-algebras", *Journal of Operator Theory* 83(2), 2020, pp. 423–445, <https://doi.org/10.7900/jot.2018oct18.2240>; read as arXiv:1808.09220v3, <https://arxiv.org/abs/1808.09220v3>: Theorem 3.6, its proof and the paragraph after it, in the paragraph "Existence of tracial states" of Section 3, and the proof of Corollary 3.7, of that version.
- J. William Helton, Kyle P. Meyer, Vern I. Paulsen and Matthew Satriano, "Algebras, synchronous games, and chromatic numbers of graphs", *New York Journal of Mathematics* 25, 2019 (cited after the paper above, Theorem 3.2(3), for the correspondence between tracial states and perfect strategies).
- Se-Jin Kim, Vern Paulsen and Christopher Schafhauser, "A synchronous game for binary constraint systems", *Journal of Mathematical Physics* 59(3), 2018, 032201, <https://doi.org/10.1063/1.4996867> (cited after the paper above).
- Igor Klep and Janez Povh, "Constrained trace-optimization of polynomials in freely noncommuting variables", *Journal of Global Optimization* 64(2), 2016, pp. 325–348, <https://doi.org/10.1007/s10898-015-0308-1> (cited after the paper above, for the semidefinite hierarchy).
