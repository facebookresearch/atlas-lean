# Existential local first-order logic of radius 3 with two data values is undecidable

Satisfiability of existential local first-order sentences of radius $3$ over finite structures whose nodes carry two data values is undecidable, although radius $2$ with two data values is decidable.

**Theorem (Bollig, Sangnier and Stietel).** The problem $\mathrm{DataSat}(\exists\text{-}3\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 2, \{{}_1{\sim}_1, {}_2{\sim}_2\})$ is undecidable: no algorithm decides, given a finite set $\Sigma$ of unary predicates and a sentence of the [existential local fragment of radius 3](local-first-order-logic-with-data.md) over $2$-data structures with the comparison symbols $\{{}_1{\sim}_1, {}_2{\sim}_2\}$, whether some finite $2$-data structure over $\Sigma$ satisfies it (Theorem 4.13 of the source).

The radius is fixed at $3$ and the number of data values at $2$; the input is the set $\Sigma$ and the sentence. For comparison, the source shows that the existential local fragment of radius $2$ with two data values and all comparison symbols is N2EXP-complete (Theorem 4.7) and that of radius $1$ is NEXP-complete for every number $Da \ge 1$ of data values (Theorem 4.10).

## Depends on

- [Local first-order logic with data](local-first-order-logic-with-data.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from $\mathrm{DataSat}(\mathrm{dFO}, 2, \{{}_1{\sim}_1, {}_2{\sim}_2\})$, undecidable by Janiczak's theorem on finite structures with two equivalence relations (Theorem 2.2 of the source). A $2$-data structure $\mathfrak A$ is extended to $\mathfrak A_{ge}$ by adding, for every pair of data values occurring in $\mathfrak A$, a node carrying that pair and marked by a fresh unary predicate $ge$; then the $3$-view of every node is the whole structure (Lemma 4.11). A sentence $\varphi$ is translated into $\exists x.\langle\!\langle T(\varphi)\rangle\!\rangle^3_x$, where $T(\varphi)$ relativizes the quantifiers to nodes not marked $ge$, and $\varphi$ is satisfiable iff its translation is (Lemma 4.12). A good expansion links a page for Janiczak's theorem in this form.

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the Satisfiability of Local First-Order Logics with Data", *Logical Methods in Computer Science* 20(3), 2024, paper 1, pp. 1:1–1:42, <https://doi.org/10.46298/lmcs-20(3:1)2024>; numbers from arXiv:2307.00831v4, <https://arxiv.org/abs/2307.00831v4>: Theorem 2.2, Theorems 4.7 and 4.10, and Section 4.3.1 with Lemmas 4.11 and 4.12 and Theorem 4.13.
- B. Bollig, A. Sangnier and O. Stietel, "On the existential fragments of local first-order logics with data", in *Proceedings of GandALF 2022*, Electronic Proceedings in Theoretical Computer Science 370, 2022, pp. 1–16, doi:10.4204/EPTCS.370.1 (the conference version, Theorem 6 of arXiv:2209.10309v1).
