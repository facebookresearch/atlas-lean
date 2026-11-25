# Henkin semantics for second-order logic

This node covers second-order logic with full and with Henkin semantics, and the contrast between
them.

In full semantics, second-order variables of arity $n$ range over all $n$-ary relations on the
domain. In a general model they range over a designated collection of relations of each arity; in the
cited survey, a Henkin model is a general model that satisfies all the axioms of second-order logic,
including the comprehension axiom schema and the axioms of choice. With respect to
Henkin models in this sense, a second-order sentence follows from the axioms exactly when it is true
in all Henkin models (Henkin), and the compactness theorem holds. With respect to full semantics, compactness fails and no
completeness theorem holds.

## Expansion

A sound expansion has separate pages for:

1. the syntax with relation variables of every finite arity, full semantics, and general and
   Henkin models, with comprehension and choice as explicit conditions on the collections (an
   arbitrary collection of subsets is not a Henkin model); a variant requiring comprehension only
   needs its own source;
2. soundness and completeness for Henkin models, and compactness for Henkin models;
3. the failure of compactness and of completeness for full semantics;
4. a first milestone for the monadic fragment: soundness and then Henkin completeness of a
   monadic second-order sequent calculus for collections of sets closed under the comprehension
   instances the calculus uses, with assignments landing in the admitted collection;
5. truth-preserving embeddings into general second-order logic of existential second-order logic
   and of monadic second-order logic on finite words, which are fragments with their own results.

Items 4 and 5 are separate obligations; a survey of full versus Henkin semantics does not discharge
them.

## Sources

- J. Väänänen, *Second-order and higher-order logic*, Stanford Encyclopedia of Philosophy,
  substantive revision 31 August 2024, §5.1, §5.2, §7.3 and §9.1.
  <https://plato.stanford.edu/entries/logic-higher-order/>
