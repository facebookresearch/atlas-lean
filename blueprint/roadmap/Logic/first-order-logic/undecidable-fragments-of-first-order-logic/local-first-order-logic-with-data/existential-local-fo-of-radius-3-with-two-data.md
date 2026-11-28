# Existential local first-order logic of radius 3 with two data values is undecidable

Satisfiability of existential local first-order sentences of radius $3$ over finite structures whose nodes carry two data values is undecidable, although radius $2$ with two data values is decidable.

**Theorem (Bollig, Sangnier and Stietel).** The problem $\mathrm{DataSat}(\exists\text{-}3\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 2)$ is undecidable: no algorithm decides, given a finite set $\Sigma$ of unary predicates and a sentence of the [existential local fragment of radius 3](local-first-order-logic-over-data-structures.md), whether some finite $2$-data structure over $\Sigma$ satisfies it.

The radius is fixed at $3$ and the number of data values at $2$; the input is the set $\Sigma$ and the sentence. For comparison, the source shows that the existential local fragment of radius $2$ with two data values is N2EXPTIME-complete and that of radius $1$ is NEXPTIME-complete for every number of data values.

## Depends on

- [Local first-order logic over data structures](local-first-order-logic-over-data-structures.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from satisfiability of full first-order logic over finite $2$-data structures, $\mathrm{DataSat}(\mathrm{dFO}, 2)$, which is undecidable by Janiczak's theorem on finite structures with two equivalence relations. Every $2$-data structure can be realized as the radius-$3$ ball of a node in a larger $2$-data structure, using an additional unary predicate to mark the original nodes; a sentence $\varphi$ is translated into $\exists x.\langle T(\varphi)\rangle^3_x$, where $T(\varphi)$ relativizes $\varphi$ to the marked nodes, and $\varphi$ is satisfiable iff its translation is.

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the existential fragments of local first-order logics with data", in *Proceedings of GandALF 2022*, Electronic Proceedings in Theoretical Computer Science 370, 2022, pp. 1–16, doi:10.4204/EPTCS.370.1; read as arXiv:2209.10309v1, <https://arxiv.org/abs/2209.10309v1>: Theorem 6 of arXiv:2209.10309v1 and Section 4.1, with Theorem 5 (from Janiczak) and Theorem 3 for the decidable case.
