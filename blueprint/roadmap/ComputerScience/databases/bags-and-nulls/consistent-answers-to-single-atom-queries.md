# Consistent answers to single-atom queries

Let $q$ be a Boolean query consisting of one atom $R(\vec s, \vec t)$, where $\vec s$ fills the key positions and the terms are variables or
constants; a fact is an instance of the atom if some substitution of its variables maps the atom to the fact. For every finite instance $db$ over a
schema with one primary key per relation, $q$ holds in every repair of $db$ if and only if some $R$-block of $db$ consists only of instances of the
atom. In particular $\mathrm{CERTAINTY}(q)$ is expressible in first-order logic.

## Proof

A repair satisfies $q$ exactly when it contains an instance of the atom. If some block consists only of instances, every repair contains one of its
facts. If no block qualifies, choose from every $R$-block a fact that is not an instance and one fact from every other block: this is a repair with no
instance, so $q$ fails there. Being an instance is a conjunction of equalities (constant positions, repeated variables), so the condition is the
first-order sentence $\exists \vec x\, \big(\exists \vec y\, R(\vec x, \vec y) \wedge \forall \vec y\, (R(\vec x, \vec y) \to \theta(\vec x, \vec y))\big)$ with $\theta$ that
conjunction.

## Depends on

- [Repairs and consistent query answering under primary keys](repairs-and-consistent-query-answering-under-primary-keys.md)

## Proof depends on

- [Repairs are block selections](repairs-are-block-selections.md)

## Sources

- P. Koutris and J. Wijsen, *A trichotomy in the data complexity of certain query answering for conjunctive queries*, arXiv:1501.07864v1, Section 3 (blocks, repairs and CERTAINTY(q)). Background reference. <https://arxiv.org/pdf/1501.07864v1>
