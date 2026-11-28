# Satisfiability of stepwise removal logic is undecidable

The satisfiability problem for the modal logic of stepwise removal with two accessibility relations is undecidable, even though its validities are recursively axiomatizable and its model checking is PSPACE-complete.

**Theorem (van Benthem, Mierzewski and Zaffora Blando).** The satisfiability problem for the [modal logic of stepwise removal](modal-logic-of-stepwise-removal.md) over models with two binary accessibility relations $R_u$ and $R_r$ is undecidable: no algorithm decides, given a formula built from proposition letters with $\neg$, $\vee$, $\Diamond_u$, $\Diamond_r$ and $\langle -\varphi\rangle\psi$, whether it holds at some point of some model $(W, R_u, R_r, V)$.

The source remarks that the two diamonds can be reduced to one by standard techniques (Kracht and Wolter), without giving details, and that the argument also works when the universal modality is replaced by a spypoint; these remarks are not part of the theorem. Since MLSR translates into first-order logic, its validities are recursively enumerable, so satisfiability is co-r.e.; the theorem shows it is not decidable.

## Depends on

- [Modal logic of stepwise removal](modal-logic-of-stepwise-removal.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Given a finite set $\mathcal{T}$ of tile types, with a letter $t_i$ for each type, the proof writes a formula $\varphi_\mathcal{T}$ that is satisfiable iff $\mathcal{T}$ tiles $\mathbb{N} \times \mathbb{N}$. It uses the universal modality $\mathsf{U}$, definable in MLSR. The removal operator is what makes the grid rigid: $\mathsf{U}\langle -\top\rangle(\Box_u\bot \wedge \Diamond_r\top)$ says that at every point the deletion of a single other point can remove all $R_u$-successors while keeping an $R_r$-successor; with its mirror image this forces $R_u$ and $R_r$ to be functions (exactly one successor each) whose values at a point differ. A similar conjunct, $\mathsf{U}\langle -\top\rangle(\Diamond_r\Box_u\bot \wedge \Diamond_u\Box_r\bot)$, forces the $R_u$-successor of the $R_r$-successor to coincide with the $R_r$-successor of the $R_u$-successor. The remaining conjuncts say, under $\mathsf{U}$, that each point carries exactly one tile and that vertically and horizontally adjacent tiles match.

## Sources

- J. van Benthem, K. Mierzewski and F. Zaffora Blando, "The modal logic of stepwise removal", *The Review of Symbolic Logic* 15(1):36–63, 2022, doi:10.1017/S1755020320000258; read as arXiv:2103.05117v1, <https://arxiv.org/abs/2103.05117v1>: Theorem 5.3 of arXiv:2103.05117v1 and its proof in Section 5.2.
