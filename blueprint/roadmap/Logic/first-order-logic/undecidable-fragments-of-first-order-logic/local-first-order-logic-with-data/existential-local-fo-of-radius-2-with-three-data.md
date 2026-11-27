# Existential local first-order logic of radius 2 with three data values is undecidable

Satisfiability of existential local first-order sentences of radius $2$ over finite structures whose nodes carry three data values is undecidable, although the same radius with two data values is decidable.

**Theorem (Bollig, Sangnier and Stietel).** The problem $\mathrm{DataSat}(\exists\text{-}2\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 3)$ is undecidable: no algorithm decides, given a finite set $\Sigma$ of unary predicates and a sentence of the [existential local fragment of radius 2](local-first-order-logic-over-data-structures.md) over $3$-data structures, whether some finite $3$-data structure over $\Sigma$ satisfies it.

The radius is fixed at $2$ and the number of data values at $3$. With two data values the same fragment is N2EXPTIME-complete (Theorem 3 of the source).

## Depends on

- [Local first-order logic over data structures](local-first-order-logic-over-data-structures.md)

## Proof depends on

None.

## Expansion

The proof reduces from $\mathrm{DataSat}(\mathrm{dFO}, 2)$, undecidable by Janiczak's theorem (1953), as the source recalls. A $2$-data structure $\mathfrak{A}$ satisfying $\varphi$ is extended to a $3$-data structure by giving every node the same third value $0$; the shared third value puts every node into the radius-$2$ view of every other node, so the view of any node is the whole structure and $\exists x.\langle\varphi\rangle^2_x$ holds. Conversely, if $\exists x.\langle\varphi\rangle^2_x$ holds, the radius-$2$ view of a witness, with the third value forgotten, is a $2$-data structure satisfying $\varphi$. Hence $\varphi$ is satisfiable iff $\exists x.\langle\varphi\rangle^2_x$ is.

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the existential fragments of local first-order logics with data", in *Proceedings of GandALF 2022*, Electronic Proceedings in Theoretical Computer Science 370, 2022, pp. 1–16, doi:10.4204/EPTCS.370.1; read as arXiv:2209.10309v1, <https://arxiv.org/abs/2209.10309v1>: Theorem 7 of arXiv:2209.10309v1 and the lemma preceding it in Section 4.2.
