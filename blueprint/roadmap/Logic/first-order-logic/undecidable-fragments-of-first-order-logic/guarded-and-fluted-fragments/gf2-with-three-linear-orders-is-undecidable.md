# The two-variable guarded fragment with three linear orders is undecidable

Satisfiability and finite satisfiability are undecidable for two-variable guarded formulas with three binary symbols interpreted as linear orders; the result for two-variable logic adapts to the case where the orders occur only as guards.

**Theorem (Kieroński).** For the [two-variable guarded fragment](two-variable-guarded-fragment.md) $\mathrm{GF}^2$ extended with three special symbols interpreted as linear orders, both the satisfiability problem and the finite satisfiability problem are undecidable. The undecidability proof for two-variable logic with three linear orders adapts to the case where the order symbols occur only as guards.

With one linear order, two-variable logic is NExpTime-complete (Otto). With two linear orders, finite satisfiability is in 2NExpTime (Zeume and Harwath), and decidability of general satisfiability is open in the overview of Kieroński and Tendera. Linear orders are an exception among special relations: for the others, restricting them to guards restores decidability.

## Depends on

- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Kieroński reduces tiling problems (Section 2 of the original paper). By Lemma 3 there, it suffices to give a two-variable sentence $\eta$ that the $\mathbb Z \times \mathbb Z$ grid and arbitrarily large finite tori, expanded by three linear orders and unary predicates, satisfy, and all of whose models with three linear orders are grid-like; the paper builds such an $\eta$ from a $4 \times 6$ repeating pattern of unary predicates and makes it guarded by using the total orders as guards (Theorem 6 and the remark after it). A good expansion links the tiling problem, the undecidability of tiling the periodic tori that finite satisfiability needs, and a page for Lemma 3. The decidability of an extension depends on the number and kind of special relations, and on whether they may occur outside guards.

## Sources

- E. Kieroński, "Decidability issues for two-variable logics with several linear orders", in *Computer Science Logic (CSL 2011)*, Leibniz International Proceedings in Informatics 12, Schloss Dagstuhl, 2011, pp. 337–351, doi:[10.4230/LIPIcs.CSL.2011.337](https://doi.org/10.4230/LIPIcs.CSL.2011.337) ; read in the open-access version: Section 2 (Lemmas 2 and 3, the construction of $\eta$) and Theorem 6 and Corollary 7 (the statement for $\mathrm{GF}^2$ with the orders used only in guards).

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Table I (rows "1 linear order", "2 linear orders" and "3 linear orders") and the paragraph after Table I.
