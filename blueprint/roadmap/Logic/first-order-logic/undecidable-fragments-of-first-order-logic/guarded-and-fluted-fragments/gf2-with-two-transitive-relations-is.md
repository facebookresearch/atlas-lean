# The two-variable guarded fragment with two transitive relations is undecidable

Satisfiability and finite satisfiability are undecidable for two-variable guarded formulas in which two binary symbols must denote transitive relations, as soon as these symbols may occur outside guards.

**Theorem (Kieroński).** For the [two-variable guarded fragment](two-variable-guarded-fragment.md) $\mathrm{GF}^2$ extended with two special binary symbols interpreted as transitive relations, both the satisfiability problem and the finite satisfiability problem are undecidable.

The survey also credits Kazakov (doctoral thesis, 2006) with this result. With a single transitive relation both problems are 2ExpTime-complete (satisfiability: Kieroński; finite satisfiability: Kieroński and Tendera). With any number of transitive relations that occur only as guards, satisfiability is 2ExpTime-complete (Szwast and Tendera; Kieroński).

## Depends on

- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The Kieroński–Tendera survey lists this case among the undecidable extensions of $\mathrm{GF}^2$ by distinguished relations, for both satisfiability and finite satisfiability, and refers to the original paper for the proof. The decidability of an extension depends on the number and kind of special relations, and on whether they may occur outside guards.

## Sources

- E. Kieroński, "Results on the guarded fragment with equivalence or transitive relations", in *Computer Science Logic (CSL 2005)*, Lecture Notes in Computer Science 3634, Springer, 2005, pp. 309–324, doi:[10.1007/11538363_22](https://doi.org/10.1007/11538363_22) (original source, cited as recalled in the survey).

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Table I (rows "2 transitive r." and "1 transitive r.").
