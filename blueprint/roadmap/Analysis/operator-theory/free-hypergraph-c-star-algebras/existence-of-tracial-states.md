# Existence of a tracial state on a free hypergraph C*-algebra is undecidable

No algorithm decides, given a finite hypergraph, whether its free hypergraph C*-algebra has a tracial state; the absence of a tracial state is semi-decidable, so the problem has the Turing degree of the halting problem.

**Theorem (Fritz).** There is no algorithm to determine, for a given finite hypergraph $H$, whether $C^*(H)$ has a tracial state.

A tracial state is a positive linear functional $\tau$ with $\tau(1) = 1$ and $\tau(ab) = \tau(ba)$ for all $a, b$. If $C^*(H)$ has no tracial state, a hierarchy of semidefinite programs detects this, so the complement of the problem is semi-decidable.

## Depends on

- [Free hypergraph C*-algebras](free-hypergraph-c-star-algebra.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [Perfect commuting strategies and the synchronous game algebra](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/perfect-strategies-and-synchronous-game-algebra.md)

## Expansion

The proof uses "Existence of a perfect commuting-operator strategy for a linear system game is undecidable", which has no page on main yet; link it once its page lands.

Every C\*-algebra of a synchronous nonlocal game is, constructively, a free hypergraph C\*-algebra (Theorem 2.19 of the source), so it suffices to treat game algebras. Such an algebra has a tracial state exactly when the game has a perfect commuting-operator strategy (Paulsen, Severini, Stahlke, Todorov and Winter), and the synchronous games built from binary constraint systems (Kim, Paulsen and Schafhauser) reduce Slofstra's undecidability theorem for perfect commuting-operator strategies of binary constraint system games to the question. The correspondence between tracial states and perfect strategies and Slofstra's theorem, in its form for linear system games, are linked above; the hypergraph form of synchronous game algebras (Theorem 2.19 of the source) and the synchronous games of binary constraint systems have no pages yet.

## Sources

- Tobias Fritz, "Curious properties of free hypergraph C*-algebras", *Journal of Operator Theory* 83(2), 2020, pp. 423–445, <https://doi.org/10.7900/jot.2018oct18.2240>; read as arXiv:1808.09220v3, <https://arxiv.org/abs/1808.09220v3>: Theorem 3.6, its proof and the paragraph after it, in the paragraph "Existence of tracial states" of Section 3 of that version.
