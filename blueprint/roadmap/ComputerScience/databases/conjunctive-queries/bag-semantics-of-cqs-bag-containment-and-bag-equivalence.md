# Bag semantics of CQs: bag containment and bag equivalence

This node collects the bag semantics of conjunctive queries and the characterization of bag
equivalence.

## Expansion

A sound expansion has separate pages for:

1. **Bag semantics.** For a conjunctive query without inequalities, in the syntax of the cited source,
   and a bag database, the multiplicity of an answer tuple is the sum, over satisfying assignments of the
   body variables that produce it, of the product over the body atoms, counted with repetition, of the
   multiplicities of their images; a repeated body atom contributes its fact's multiplicity once per
   occurrence.
2. **Containment and equivalence.** $Q \subseteq_b Q'$ when the multiplicities of $Q$ are pointwise at most
   those of $Q'$ on every bag database; bag equivalence is containment both ways. Set-semantics
   homomorphism criteria do not transfer to bag containment.
3. **Bag equivalence is isomorphism.** Two conjunctive queries are bag-equivalent if and only if they are
   isomorphic, that is, a one-to-one renaming of variables maps the head onto the head and the body,
   as a bag of atoms, onto the body (Chaudhuri–Vardi, Theorem 5.2), so deciding bag equivalence is polynomial-time equivalent to
   graph isomorphism (Corollary 5.3).

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Depends on

- [Bag relations and bag relational algebra](../bags-and-nulls/bag-relations-and-bag-relational-algebra.md)

## Sources

- Optimization of Real Conjunctive Queries (Chaudhuri, Vardi), PODS 1993, Theorem 5.2 and Corollary 5.3. <https://web.cs.ucdavis.edu/~green/courses/ecs289f-w10/p59-chaudhuri.pdf>
- Bag Query Containment and Information Theory (Abo Khamis, Kolaitis, Ngo, Suciu), arXiv:1906.09727 — arXiv (PODS 2020). <https://arxiv.org/pdf/1906.09727> Background reference.
