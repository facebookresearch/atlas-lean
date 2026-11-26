# Dependencies and the chase

- [Chasing tableau queries with functional and join dependencies](chasing-tableau-queries-with-functional-and-join-dependencie.md)
- [The chase for functional and inclusion dependencies](chase-for-functional-and-inclusion-dependencies/README.md)
- [Containment of tableau queries under functional and join dependencies via the chase](containment-under-fds-and-jds-via-the-chase.md)
- [Inference rules for functional and multivalued dependencies are sound and complete](fd-and-mvd-inference-rules-are-sound-and-complete.md)
- [Inference rules for multivalued dependencies alone are sound and complete](mvd-inference-rules-are-sound-and-complete.md)
- [Complexity of implication of join dependencies](complexity-of-implication-of-join-dependencies.md)
- [A join dependency is acyclic if and only if it is equivalent to a set of multivalued dependencies](acyclic-join-dependencies-are-equivalent-to-sets-of-mvds.md)
- [Satisfaction of an inclusion dependency](inclusion-dependencies-and-finite-implication.md)
- [Implication of inclusion dependencies is PSPACE-complete](implication-of-inclusion-dependencies-is-pspace-complete.md)
- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Guarded tuple-generating dependencies](guarded-tgds/README.md)
- [Implication of full dependencies is decidable](implication-of-full-dependencies-is-decidable.md)
- [Implication of embedded dependencies is undecidable](implication-of-embedded-dependencies-is-undecidable.md)
- [Weakly acyclic dependencies have polynomially bounded chase](weakly-acyclic-dependencies-have-polynomially-bounded-chase.md)
- [Finite and unrestricted implication of functional and inclusion dependencies](finite-and-unrestricted-implication-of-functional-and-inclusion.md)
- [Successful terminating chases yield universal models](successful-terminating-chases-yield-universal-models.md)
- [Data exchange: universal solutions and certain answers of UCQs](data-exchange-universal-solutions-and-certain-answers-of-ucq.md)
- [The core of the universal solutions in data exchange](core-of-the-universal-solutions.md)
- [The core of the universal solutions is computable in polynomial time for target egds](core-of-universal-solutions-in-polynomial-time.md)
- [Certain answers on universal solutions are the null-free answers on the core](certain-answers-on-universal-solutions-via-the-core.md)
- [Multivalued and join dependencies](multivalued-and-join-dependencies/README.md)

## Instances and projection inclusion

- [Relational schema](relational-schema.md)
- [Database instance](instance.md)
- [Finite database instance](is-finite.md)
- [Active domain of a database instance](active-domain.md)
- [Finite extents and finite active domain](is-finite-iff-finite-active-domain.md)
- [Ordered projection of a relation](ordered-projection.md)
- [Syntax of an inclusion dependency](ind.md)
- [A joint witness for a projected row](holds-in-iff-exists-row.md)
- [Reflexivity of projection inclusion](holds-in-refl.md)
- [Transitivity of projection inclusion](holds-in-trans.md)

## Implication of schema dependencies

A set of hypotheses may contain both functional and inclusion dependencies. Implication asks whether every whole instance satisfying all hypotheses also satisfies the conclusion. Unrestricted and finite implication use the same value domain ([*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Definition 9.2.1, p. 198). Taking the natural numbers as values recovers the book's countably infinite domain (§3.1). Finite implication restricts the relation extents, not the value domain. With finitely many relation names and finitely many attributes per relation, the extents are finite exactly when the active domain, the set of values occurring in the rows, is finite.

- [Functional and inclusion dependencies on a schema](dependency.md)
- [Satisfaction of a schema dependency](holds-in-2.md)
- [Unrestricted implication of dependencies](implies.md)
- [Finite implication of dependencies](finitely-implies.md)
- [Unrestricted implication gives finite implication](finitely-implies-of-implies.md)
- [Proof ingredients for finite and unrestricted implication](implication-proofs/README.md)
