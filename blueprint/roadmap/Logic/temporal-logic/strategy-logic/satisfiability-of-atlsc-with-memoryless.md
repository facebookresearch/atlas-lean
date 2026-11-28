# Satisfiability of ATLsc with memoryless strategies is undecidable

When the strategy quantifiers of ATL with strategy contexts range over memoryless strategies only, satisfiability becomes undecidable, even over turn-based game structures, where full ATLsc satisfiability is decidable.

**Theorem (Laroussinie and Markey).** The satisfiability problem for $\mathrm{ATL}^0_{sc}$, [ATL with strategy contexts](atl-with-strategy-contexts.md) in which $\langle{\cdot} A {\cdot}\rangle$ quantifies over memoryless strategies, is undecidable, even when the models are restricted to turn-based concurrent game structures.

This is Theorem 14 of the source, which proves it in detail for infinite-state turn-based games by encoding the tiling of the quadrant and indicates that the finite-state turn-based case follows by similar, more involved, ideas encoding the tiling of all finite grids. The same method shows that satisfiability of strategy logic with memoryless strategy quantification, $\mathrm{SL}^0$, is undecidable even over turn-based structures (Theorem 17 of the source, with proof sketched). By contrast, satisfiability of $\mathrm{ATL}_{sc}$ with arbitrary strategies over turn-based games is decidable, by the reduction to quantified CTL* of Theorem 10, though non-elementary (Theorem 11).

## Depends on

- [ATL with strategy contexts](atl-with-strategy-contexts.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof adapts French's undecidability proof for quantified CTL under the structure semantics, which encodes the tiling of the quadrant $\mathbb N \times \mathbb N$ by a finite set of tiles with horizontal and vertical compatibility relations. A formula with two players forces a grid-shaped turn-based game: main states controlled by the second player form the grid, each with a right and a top neighbor distinguished by alternating propositions $v_1, v_2$, and further tile states carry the tiles. Quantifying over memoryless strategies amounts to selecting transitions of the graph itself, which plays the role of the propositional quantifiers of quantified CTL under the structure semantics; this is the added expressive power that plain $\mathrm{ATL}_{sc}$ lacks on turn-based games. The proof uses the quadrant form of the tiling problem, tilings of $\mathbb N \times \mathbb N$, which follows from the plane form by compactness; a good expansion links a page for it.

## Sources

- F. Laroussinie and N. Markey, "Satisfiability of ATL with strategy contexts", in *Proceedings of the Fourth International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2013)*, Electronic Proceedings in Theoretical Computer Science 119, 2013, pp. 208–223, <https://doi.org/10.4204/EPTCS.119.18>; numbers from arXiv:1307.4478v1, <https://arxiv.org/abs/1307.4478v1>: Section 6: Theorem 14 and its proof (Figure 1); Section 7.1: Theorem 17; Section 5: Theorems 10 and 11.
- T. French, "Decidability of quantified propositional branching time logics", in *AI 2001: Advances in Artificial Intelligence (14th Australian Joint Conference on Artificial Intelligence)*, Lecture Notes in Computer Science 2256, Springer, 2001, pp. 165–176, <https://doi.org/10.1007/3-540-45656-2_15>: undecidability of quantified CTL under the structure semantics, the proof adapted here; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (proof of Theorem 14).
