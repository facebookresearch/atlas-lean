# Satisfiability of quantified announcement logics is undecidable

For two or more agents, satisfiability is undecidable for arbitrary public announcement logic APAL, group announcement logic GAL and coalition announcement logic CAL; with a single agent all three are decidable.

**Theorem (Ågotnes, van Ditmarsch and French).** Let the set $A$ of agents have at least two elements. Then the satisfiability problem for each of the [logics APAL, GAL and CAL](quantified-public-announcement-logics.md) over $A$ is undecidable: no algorithm decides, given a formula of the respective language, whether it holds at some world of some model with an equivalence relation for each agent. When $|A| = 1$, all three satisfiability problems are decidable.

The proof shows more: the satisfiability problems are equivalent to the complement of a tiling problem and therefore are not recursively enumerable, so none of the three logics has a recursively enumerable set of validities. Undecidability of APAL was first shown by French and van Ditmarsch (2008) and of GAL by Ågotnes, van Ditmarsch and French (2014); the source treats all three uniformly and is the first proof for CAL. The version read corrects an error in the published proof of the group case (the definition of the formula $c_{ga}(X)$), pointed out by Asami; the statement is unchanged.

## Depends on

- [Arbitrary, group and coalition announcement logics](quantified-public-announcement-logics.md)
- [Epistemic models](model.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Given a finite set $\Gamma$ of tiles, the proof builds for each logic a formula that is satisfiable iff $\Gamma$ tiles $\mathbb{N} \times \mathbb{N}$ (Lemmas 6.2 and 6.3). The construction has three steps: force any model of the formula to contain a grid-like structure, a checkerboard whose squares are labeled by the four card suits in a regular pattern, with the agents' relations linking each square to its neighbors; define a formula that plays the role of common knowledge over this grid; and use atoms for tiles to say that it is common knowledge that adjacent tiles have matching sides. The quantified announcements are what close the grid: a failure of the grid shape would be exposed by some announcement (for GAL and CAL, one known to the announcing agents) that the formula rules out. The single-agent case reduces to epistemic logic: there the arbitrary announcement operator is definable (Balbiani et al.), and the group and coalition operators are handled similarly.

## Sources

- T. Ågotnes, H. van Ditmarsch and T. French, "The undecidability of quantified announcements", *Studia Logica* 104(4):597–640, 2016, doi:10.1007/s11225-016-9657-0; read as the corrected version arXiv:2405.15671v2, <https://arxiv.org/abs/2405.15671v2>: Theorem 6.4 of arXiv:2405.15671v2, with Lemmas 6.2 and 6.3.
