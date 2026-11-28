# Categorical semantics of BI

This node covers the semantics of BI proofs in bicartesian doubly closed categories, which O'Hearn and Pym give alongside natural deduction for BI.

A *doubly closed category* (DCC) is a category with two monoidal closed structures; it is *cartesian* if one of them is cartesian and the other symmetric monoidal, and *bicartesian* if in addition it has finite coproducts. An interpretation assigns an object to each propositional letter and extends to propositions and to bunches, sending "," to the symmetric monoidal product and ";" to the cartesian product. O'Hearn and Pym state soundness and completeness at the level of provability, that $\Gamma \vdash \varphi$ is provable in BI if and only if, for every such category and interpretation, the hom-set from the interpretation of $\Gamma$ to that of $\varphi$ is non-empty (their Proposition 4, with the published erratum that "DCC" there should read "bicartesian DCC"), and indicate a stronger form relating the equality of proofs induced by this semantics to an equational theory of proofs. Their Example 5 ($\mathbf{Set} \times \mathbf{Set}$, and more generally $\mathbf{Set}^{\mathcal{M}}$ for a commutative monoid $\mathcal{M}$) shows that the two implications are not interderivable, and Day's construction (their Section 3.1) gives a symmetric monoidal closed structure on presheaf categories, the categorical form of the elementary Kripke resource semantics: for a symmetric monoidal category $\mathcal{C}$, the presheaf category $\mathbf{Set}^{\mathcal{C}^{op}}$ is a bicartesian DCC (their Proposition 6, credited to Day).

## Depends on

- [Natural deduction for BI](natural-deduction-for-bi.md)

## Proof depends on

None.

## Expansion

This node is still to expand. A good expansion states the definition of bicartesian doubly closed categories and the interpretation of NBI derivations as morphisms, soundness and completeness at the level of provability, the non-interconvertibility of the two implications through Example 5, and Day's construction, each on its own page, with prerequisites for monoidal closed and cartesian closed categories.

## Sources

- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 3 (doubly closed categories, Proposition 4 and the stronger form after it, Example 5) and Section 3.1 (Day's construction and Proposition 6). Erratum to Proposition 4 as listed on the second author's BI page, <https://www.cantab.net/users/david.pym/BI.htm>.
