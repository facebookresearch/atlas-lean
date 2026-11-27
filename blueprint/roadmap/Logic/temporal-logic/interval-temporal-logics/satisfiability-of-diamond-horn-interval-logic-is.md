# Satisfiability of diamond Horn interval logic is undecidable

Satisfiability of Horn formulas of the Halpern–Shoham interval logic that use only diamonds is undecidable over every class of linear orders containing an infinite order, and over finite orders, under either semantics.

**Theorem (Bresolin, Kurucz, Muñoz-Velasco, Ryzhikov, Sciavicco and Zakharyaschev).** For the fragment $\mathcal{HS}^\Diamond_{\mathit{horn}}$ of [Horn formulas of the Halpern–Shoham logic](horn-fragments-of-the-halpern-shoham-logic.md) without box operators, under arbitrary semantics:

1. for any class $\mathcal{C}$ of linear orders containing an infinite order, $\mathcal{C}$-satisfiability of $\mathcal{HS}^\Diamond_{\mathit{horn}}$-formulas is undecidable;
2. $\mathrm{Fin}$-satisfiability of $\mathcal{HS}^\Diamond_{\mathit{horn}}$-formulas, over finite linear orders, is undecidable.

The same source proves that the box-only fragment $\mathcal{HS}^\Box_{\mathit{horn}}$, tractable over dense orders, becomes undecidable over discrete orders under the irreflexive semantics (Theorem 4.5), and that the core fragment with binary clauses is undecidable under the irreflexive semantics (Theorem 4.4).

## Depends on

- [Horn fragments of the Halpern–Shoham logic](horn-fragments-of-the-halpern-shoham-logic.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Clause 1 reduces non-halting of Turing machines on the empty input ($\Pi^0_1$-hard): for an order with an infinite ascending chain, Horn clauses with diamonds force an infinite grid-like structure of intervals in the two-dimensional representation of intervals as points $(x, y)$ with $x \leq y$, on which successive configurations are laid out, and a final clause forbids the halting state; the case of an infinite descending chain is symmetric. Clause 2 adapts the construction to finite orders. The key point, as for products of linear orders, is a "unique controllable diagonal" that Horn clauses with diamonds can still enforce.

## Sources

- D. Bresolin, A. Kurucz, E. Muñoz-Velasco, V. Ryzhikov, G. Sciavicco and M. Zakharyaschev, "Horn fragments of the Halpern–Shoham interval temporal logic", *ACM Transactions on Computational Logic* 18(3), Article 22, 2017, 39 pp., doi:10.1145/3105909; read as arXiv:1604.03515v5, <https://arxiv.org/abs/1604.03515v5>: Theorem 4.3 of arXiv:1604.03515v5 and its proof in Section 4, with Theorems 4.4 and 4.5.
