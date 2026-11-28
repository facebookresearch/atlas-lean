# Existential local first-order logic of radius 2 with three data values is undecidable

Satisfiability of existential local first-order sentences of radius $2$ over finite structures whose nodes carry three data values is undecidable, although the same radius with two data values is decidable.

**Theorem (Bollig, Sangnier and Stietel).** The problem $\mathrm{DataSat}(\exists\text{-}2\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 3, \{{}_1{\sim}_1, {}_2{\sim}_2, {}_3{\sim}_3\})$ is undecidable: no algorithm decides, given a finite set $\Sigma$ of unary predicates and a sentence of the [existential local fragment of radius 2](local-first-order-logic-with-data.md) over $3$-data structures with the comparison symbols $\{{}_1{\sim}_1, {}_2{\sim}_2, {}_3{\sim}_3\}$, whether some finite $3$-data structure over $\Sigma$ satisfies it (Theorem 4.15 of the source).

The radius is fixed at $2$ and the number of data values at $3$. With two data values and all comparison symbols the same fragment is N2EXP-complete (Theorem 4.7 of the source).

## Depends on

- [Local first-order logic with data](local-first-order-logic-with-data.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from $\mathrm{DataSat}(\mathrm{dFO}, 2, \{{}_1{\sim}_1, {}_2{\sim}_2\})$, undecidable by Janiczak's theorem on finite structures with two equivalence relations (Theorem 2.2 of the source). A $2$-data structure satisfying $\varphi$ is extended to a $3$-data structure by giving every node the same third value $0$; the shared third value puts every node into the radius-$2$ ball of every other node, so the $2$-view of any node is the whole structure and $\exists x.\langle\!\langle\varphi\rangle\!\rangle^2_x$ holds. Conversely, if $\exists x.\langle\!\langle\varphi\rangle\!\rangle^2_x$ holds, the $2$-view of a witness, with the third value forgotten, is a $2$-data structure satisfying $\varphi$ (Lemma 4.14). A good expansion links a page for Janiczak's theorem in this form.

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the Satisfiability of Local First-Order Logics with Data", *Logical Methods in Computer Science* 20(3), 2024, paper 1, pp. 1:1–1:42, <https://doi.org/10.46298/lmcs-20(3:1)2024>; numbers from arXiv:2307.00831v4, <https://arxiv.org/abs/2307.00831v4>: Theorem 2.2, Theorem 4.7, and Section 4.3.2 with Lemma 4.14 and Theorem 4.15.
- B. Bollig, A. Sangnier and O. Stietel, "On the existential fragments of local first-order logics with data", in *Proceedings of GandALF 2022*, Electronic Proceedings in Theoretical Computer Science 370, 2022, pp. 1–16, doi:10.4204/EPTCS.370.1 (an earlier conference version, Theorem 7 of arXiv:2209.10309v1, whose logic is defined without the comparison set $\Gamma$: its data graph joins the data values of one node and equal data values, so it does not state the $\Gamma$ forms above).
