# QCDCL and Q-resolution are incomparable

Classical QCDCL, with decisions in quantifier order and propagation with universal reduction, and Q-resolution are exponentially incomparable.

**Theorem.** The proof systems $\mathsf{Q\text{-}Res}$ and $\mathsf{QCDCL}^{\mathsf{LEV\text{-}ORD}}_{\mathsf{RED}}$ are incomparable: the formulas $\mathrm{QParity}_n$ have polynomial-size $\mathsf{QCDCL}^{\mathsf{LEV\text{-}ORD}}_{\mathsf{RED}}$ refutations but need exponential-size Q-resolution refutations, while the formulas $\mathrm{Trapdoor}_n$ have constant-size Q-resolution refutations but need exponential-size $\mathsf{QCDCL}^{\mathsf{LEV\text{-}ORD}}_{\mathsf{RED}}$ refutations.

Here $\mathrm{Trapdoor}_n$ has prefix $\exists y_1, \dots, y_{s_n}\, \forall w\, \exists t, x_1, \dots, x_{s_n}\, \forall u$ and matrix consisting of the pigeonhole clauses $\mathrm{PHP}^{n+1}_n(x_1, \dots, x_{s_n})$ together with, for $i = 1, \dots, s_n$, the clauses $\overline{y}_i \lor x_i \lor u$, $y_i \lor \overline{x}_i \lor u$, $y_i \lor w \lor t$, $y_i \lor w \lor \overline{t}$, $\overline{y}_i \lor w \lor t$ and $\overline{y}_i \lor w \lor \overline{t}$.

## Expansion

In level-ordered QCDCL with reduction, every trail for $\mathrm{Trapdoor}_n$ starts with decisions on $y$ variables and, because $\mathrm{PHP}^{n+1}_n$ is unsatisfiable, reaches a conflict before $w$ is decided; the learned clauses only mention $x$, $y$ and $u$, so the run is essentially a resolution refutation of the pigeonhole formula, which is exponentially long (Haken). Q-resolution instead refutes the last four clause types directly. For $\mathrm{QParity}_n$ the source builds explicit trails whose learned clauses are long-distance Q-resolution derivations, which are not available to Q-resolution.

## Depends on

- [QCDCL proof systems](qcdcl-proof-systems.md)
- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)
- [QBF parity formulas are hard for QU-resolution but easy for expansion](parity-formulas-hard-for-qu-resolution.md)
- [Haken's lower bound for the pigeonhole principle](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Proof depends on

- [QBF parity formulas are hard for QU-resolution but easy for expansion](parity-formulas-hard-for-qu-resolution.md)
- [Haken's lower bound for the pigeonhole principle](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Definitions 4.1 and 4.5, Propositions 4.2, 4.6 and 4.7, and Theorem 4.8; policy names as in this edition).
