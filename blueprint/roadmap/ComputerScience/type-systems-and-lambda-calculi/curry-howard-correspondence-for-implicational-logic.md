# Curry–Howard correspondence for implicational logic

Natural-deduction derivations in intuitionistic implicational logic correspond to terms of the simply typed lambda calculus. A derivation of $A$ whose undischarged assumptions are labelled $x_1 : A_1, \dots, x_n : A_n$ translates to a term $t$ with $x_1 : A_1, \dots, x_n : A_n \vdash t : A$: an assumption becomes a variable, implication introduction discharging $x : B$ becomes the abstraction $\lambda x^B.\, t$, and implication elimination becomes application. Conversely every typed term determines such a derivation, and the two translations are mutually inverse, up to renaming of assumption labels and bound variables, preserving the context and the conclusion. Under this correspondence the elimination of an introduction immediately followed by an elimination is $\beta$-reduction, so normal derivations correspond to normal terms.

## Expansion

This page becomes ready once these prerequisites are stated:

- A label-preserving translation from typed terms in list contexts to natural-deduction derivations whose assumptions carry the variable labels, so that distinct variables of the same type stay distinct (proof prerequisite)
- The converse translation from natural-deduction derivations of implicational logic to typed terms (proof prerequisite)
- The two translations are mutually inverse up to renaming of assumption labels and bound variables (proof prerequisite)
- Detour elimination in natural deduction corresponds to β-reduction, so normal derivations correspond to normal terms (proof prerequisite)

## Background

- [Typed terms give natural-deduction derivations](typed-terms-give-natural-deduction-derivations.md): derivability of the type from the set of hypotheses, which forgets assumption labels and multiplicity and so cannot be inverted

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 3, "The Curry-Howard isomorphism", <https://www.paultaylor.eu/stable/prot.pdf>
- P. Wadler, "Propositions as types", *Communications of the ACM* 58(12):75–84, 2015, <https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf>
- W. A. Howard, "The formulae-as-types notion of construction", in *To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, Academic Press, 1980
