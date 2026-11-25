# Henkin completeness of Church's simple type theory

This node covers Church's simple theory of types with general (Henkin) semantics and the soundness
and completeness theorem for its natural deduction calculus, together with the failure of
completeness for standard semantics.

Types are built from a type of individuals and a type of truth values by forming function types.
The language has typed variables and constants, application, $\lambda$-abstraction, typed
quantification, equality (primitive or defined) and, in the selected presentation, typed
description operators. A general model assigns to each type a nonempty domain, the domain of the
type of truth values being exactly the two truth values, and to each function type a set of
functions between the corresponding domains, not necessarily all of them; the evaluation of terms
respects typing, application and $\beta$-conversion, and the domains are closed enough that every
$\lambda$-term denotes. Extensionality is part of the selected model class. A standard model is a
general model in which every function-type domain contains all functions. Henkin's theorem: the
calculus is sound and complete for general models, under the hypothesis conditions recorded in the
expansion.

## Expansion

A sound expansion fixes one object logic and its source theorem, and has separate pages for:
types, terms and the calculus; general and standard models with the exact closure and
extensionality conditions; soundness; and completeness for the selected hypothesis class. In the
cited journal presentation completeness is proved for sets of hypotheses that are sufficiently pure,
that is, leave infinitely many parameters of the signature unused; the cited machine-checked
development proves it at every infinite value carrier for signatures with infinitely many
parameters, needing nothing beyond well-formedness for a finite context, and, for derivability from
some finite part of an arbitrary context of open formulas, over any infinite signature once the
carrier is at least as large as the signature. These conditions are kept, not
replaced by an unconditional statement. The limits of standard semantics are a separate page. By Gödel's
incompleteness theorem, no recursively axiomatized extension of the axioms that is sound for standard
models derives every formula valid in all standard models. If the axioms include an axiom of infinity,
consistency of the extension already suffices for this conclusion. Consistency alone does not suffice
for the calculus without such an axiom: it has standard models with a finite domain of individuals,
and for such a model with computably interpreted constants, the set of formulas valid in the model is
a consistent, decidable extension of the axioms that contains every formula valid in all standard
models. Compactness also fails for standard semantics. Church's simple type theory is distinct from
rank-one polymorphic higher-order logic and from System F.

## Sources

- C. Benzmüller and P. Andrews, *Church's type theory*, Stanford Encyclopedia of Philosophy,
  substantive revision 16 January 2024, §2. <https://plato.stanford.edu/entries/type-theory-church/>
- J. Väänänen, *Second-order and higher-order logic*, Stanford Encyclopedia of Philosophy,
  substantive revision 31 August 2024: second-order logic has no complete axiomatization (a finite
  categorical axiomatization of arithmetic together with Gödel's incompleteness theorem), and an axiom
  of infinity is expressible in the empty vocabulary.
  <https://plato.stanford.edu/entries/logic-higher-order/>
- C. Benzmüller, C. E. Brown and M. Kohlhase, *Higher-order semantics and extensionality*,
  Journal of Symbolic Logic 69(4) (2004), 1027–1088, Theorem 7.3 and Corollary 7.7.
  <https://doi.org/10.2178/jsl/1102022211>
- C. Benzmüller and D. Kirchner, *A deep embedding of HOL in HOL: soundness, completeness,
  consistency*, Archive of Formal Proofs, entry abstract.
  <https://devel.isa-afp.org/entries/HOL_in_HOL_Deep.html>
