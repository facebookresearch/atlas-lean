# Two-variable guarded fragment

The two-variable guarded fragment $\mathrm{GF}^2$ consists of the first-order formulas in two variables $x, y$ in which every quantifier is relativized by an atom, its guard, that contains all free variables of the quantified formula. Extensions declare some binary symbols to denote transitive relations, equivalence relations or linear orders.

**Formulas.** $\mathrm{GF}^2$ is the two-variable [guarded fragment](guarded-fragment.md), the set of $\mathrm{GF}$ formulas in the variables $x, y$, taken here over a relational signature of unary and binary relation symbols with equality; it is the intersection of [two-variable logic](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md) $\mathrm{FO}^2$ with the guarded fragment.

**Distinguished relations.** An extension of $\mathrm{GF}^2$ may declare some binary symbols *special* and require each to be interpreted as a transitive relation, an [equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md) or a linear order, as the extension prescribes. A formula is (finitely) satisfiable if it has a (finite) model in which every special symbol has its required interpretation. Unless stated otherwise, special symbols may occur anywhere in a formula. In the variants *with special guards*, they may occur only as guards.

## Depends on

- [Guarded fragment of first-order logic](guarded-fragment.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)
- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

None.

## Expansion

$\mathrm{GF}^2$ has the finite model property and its satisfiability problem is ExpTime-complete (Grädel), while $\mathrm{FO}^2$ is NExpTime-complete. Transitivity cannot be expressed in $\mathrm{FO}^2$, so the special symbols add expressive power, and with them the finite model property can fail. Whether satisfiability stays decidable depends on how many special symbols there are and of which kind. With special guards, the fragment with any number of transitive guards is 2ExpTime-complete and the fragment with equivalence guards is NExpTime-complete.

## Sources

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Section 2 (the definition of $\mathrm{GF}^2$ and of special guards).
