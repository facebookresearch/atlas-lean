# Dependencies and the chase

- [Chasing tableau queries with functional and join dependencies](chasing-tableau-queries-with-functional-and-join-dependencie.md)
- [Satisfaction of an inclusion dependency](inclusion-dependencies-and-finite-implication.md)
- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Weakly acyclic dependencies have polynomially bounded chase](weakly-acyclic-dependencies-have-polynomially-bounded-chase.md)
- [Finite and unrestricted implication of functional and inclusion dependencies](finite-and-unrestricted-implication-of-functional-and-inclusion.md)
- [Successful terminating chases yield universal models](successful-terminating-chases-yield-universal-models.md)
- [Data exchange: universal solutions and certain answers of UCQs](data-exchange-universal-solutions-and-certain-answers-of-ucq.md)
- [Multivalued and join dependencies; 4NF](multivalued-and-join-dependencies-4nf.md)

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
