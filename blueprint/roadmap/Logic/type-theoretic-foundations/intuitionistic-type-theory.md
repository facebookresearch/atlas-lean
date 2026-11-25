# Intuitionistic type theory

This node covers intuitionistic (Martin-Löf) type theory, a formal system and foundation for
constructive mathematics. Its judgments assert that a type is well formed, that a term has a type, and
that two types or two terms are equal; its type formers include dependent products $\Pi$, dependent
sums $\Sigma$ and identity types $\mathrm{I}(A, a, b)$, so that types may depend on terms, and it is
extended by inductive (and inductive-recursive) definitions and by universes. Its models include the
groupoid model, which validates universe extensionality, a first step towards Voevodsky's univalence
axiom, and the model of the intensional theory in Kan simplicial sets, which satisfies the univalence
axiom: the map $\mathrm{I}(\mathrm{U}, A, B) \to A \simeq B$ associated with the identity eliminator is
an equivalence.

## Expansion

A sound expansion fixes one presentation (intensional or extensional, the universes and the inductive
types admitted), its judgments and rules, and then has separate pages for: the interpretation of
propositions as types; normalization and decidability of type checking for the chosen presentation,
each with its own source; the groupoid model and the failure of uniqueness of identity proofs; and the
simplicial-set model with univalence. The calculus of constructions and its strong normalization are a
separate, existing topic.

## Sources

- P. Dybjer and E. Palmgren, *Intuitionistic type theory*, Stanford Encyclopedia of Philosophy,
  substantive revision 23 September 2024, §2, §3.2, §4 and §6.5. <https://plato.stanford.edu/entries/type-theory-intuitionistic/>
