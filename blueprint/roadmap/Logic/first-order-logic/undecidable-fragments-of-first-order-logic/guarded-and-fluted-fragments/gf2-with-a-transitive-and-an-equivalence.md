# The two-variable guarded fragment with a transitive and an equivalence relation is undecidable

Satisfiability and finite satisfiability are undecidable for two-variable guarded formulas with one binary symbol interpreted as a transitive relation and another as an equivalence relation.

**Theorem (Kieroński, Michaliszyn, Pratt-Hartmann and Tendera).** For the [two-variable guarded fragment](two-variable-guarded-fragment.md) $\mathrm{GF}^2$ extended with one special symbol interpreted as a transitive relation and one interpreted as an equivalence relation, both the satisfiability problem and the finite satisfiability problem are undecidable.

Each of the two special relations alone is harmless: with one transitive relation both problems are 2ExpTime-complete, and with one equivalence relation they are NExpTime-complete (Kieroński and Otto, for full two-variable logic).

## Depends on

- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

None.

## Expansion

The Kieroński–Tendera survey lists this case among the undecidable extensions of $\mathrm{GF}^2$ by distinguished relations, for both satisfiability and finite satisfiability, and refers to the original paper for the proof. The decidability of an extension depends on the number and kind of special relations, and on whether they may occur outside guards.

## Sources

- E. Kieroński, J. Michaliszyn, I. Pratt-Hartmann and L. Tendera, "Two-variable first-order logic with equivalence closure", *SIAM Journal on Computing* 43(3):1012–1063, 2014, doi:[10.1137/120900095](https://doi.org/10.1137/120900095) (original source, cited as recalled in the survey).

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Table 1 (row "1 trans. + 1 equiv.").
