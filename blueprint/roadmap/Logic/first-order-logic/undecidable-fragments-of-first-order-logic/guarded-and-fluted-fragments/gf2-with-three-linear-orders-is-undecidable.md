# The two-variable guarded fragment with three linear orders is undecidable

Satisfiability and finite satisfiability are undecidable for two-variable guarded formulas with three binary symbols interpreted as linear orders; the result for two-variable logic adapts to the case where the orders occur only as guards.

**Theorem (Kieroński).** For the [two-variable guarded fragment](two-variable-guarded-fragment.md) $\mathrm{GF}^2$ extended with three special symbols interpreted as linear orders, both the satisfiability problem and the finite satisfiability problem are undecidable. The undecidability proof for two-variable logic with three linear orders adapts to the case where the order symbols occur only as guards.

With one linear order, two-variable logic is NExpTime-complete (Otto). With two linear orders, finite satisfiability is in 2NExpTime (Zeume and Harwath), and decidability of general satisfiability is open in the survey. Linear orders are an exception among special relations: for the others, restricting them to guards restores decidability.

## Depends on

- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The Kieroński–Tendera survey lists this case among the undecidable extensions of $\mathrm{GF}^2$ by distinguished relations, for both satisfiability and finite satisfiability, and refers to the original paper for the proof. The decidability of an extension depends on the number and kind of special relations, and on whether they may occur outside guards.

## Sources

- E. Kieroński, "Decidability issues for two-variable logics with several linear orders", in *Computer Science Logic (CSL 2011)*, Leibniz International Proceedings in Informatics 12, Schloss Dagstuhl, 2011, pp. 337–351, doi:[10.4230/LIPIcs.CSL.2011.337](https://doi.org/10.4230/LIPIcs.CSL.2011.337) (original source, cited as recalled in the survey).

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Table I (rows "1 linear order", "2 linear orders" and "3 linear orders") and the paragraph after Table I.
