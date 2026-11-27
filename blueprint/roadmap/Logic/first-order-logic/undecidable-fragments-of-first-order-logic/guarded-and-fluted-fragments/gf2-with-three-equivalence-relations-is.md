# The two-variable guarded fragment with three equivalence relations is undecidable

Satisfiability and finite satisfiability are undecidable for two-variable guarded formulas, and hence for two-variable logic, with three binary symbols interpreted as equivalence relations.

**Theorem (Kieroński and Otto).** For the [two-variable guarded fragment](two-variable-guarded-fragment.md) $\mathrm{GF}^2$ extended with three special symbols interpreted as equivalence relations, both the satisfiability problem and the finite satisfiability problem are undecidable. Since $\mathrm{GF}^2$ is contained in two-variable logic $\mathrm{FO}^2$, the same holds for $\mathrm{FO}^2$ with three equivalence relations.

With one equivalence relation the problems are NExpTime-complete and the logic has the finite model property (Kieroński and Otto, for $\mathrm{FO}^2$); with two equivalence relations they are 2ExpTime-complete for $\mathrm{GF}^2$ (satisfiability: Kieroński; finite satisfiability: Kieroński, Pratt-Hartmann and Tendera).

## Depends on

- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)

## Proof depends on

None.

## Expansion

The Kieroński–Tendera survey lists this case among the undecidable extensions of $\mathrm{GF}^2$ by distinguished relations, for both satisfiability and finite satisfiability, and refers to the original paper for the proof. The decidability of an extension depends on the number and kind of special relations, and on whether they may occur outside guards.

## Sources

- E. Kieroński and M. Otto, "Small substructures and decidability issues for first-order logic with two variables", *The Journal of Symbolic Logic* 77(3):729–765, 2012, doi:[10.2178/jsl/1344862160](https://doi.org/10.2178/jsl/1344862160) (original source, cited as recalled in the survey).

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Table 1 (rows "1 equivalence r.", "2 equivalence r." and "3 equivalence r.").
