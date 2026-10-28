# FLM reference and passage checklist

## Adopted reference

Igor Frenkel, James Lepowsky, and Arne Meurman,
*Vertex Operator Algebras and the Monster* (1988), Academic Press,
Pure and Applied Mathematics, volume 134, ISBN 978-0-12-267065-7.
See the [publisher's catalogue record](https://shop.elsevier.com/books/vertex-operator-algebras-and-the-monster/frenkel/978-0-12-267065-7)
and [series volume page](https://www.sciencedirect.com/bookseries/pure-and-applied-mathematics/vol/134).

The project adopts this book as the primary construction reference. Its relevant
chapter text has not been inspected for this PR. There are no claimed chapter
numbers, theorem numbers, page quotations, or complete source-derived proof
dependencies. The structural and numerical targets come from the agreed project
scope, recorded in [scope.md](scope.md).

## Passages to obtain before fine decomposition

For each item, record the edition, page or section, definition/theorem identifier,
precise statement, proof outline, and every cited prerequisite:

1. The lattice/code construction, lattice central extension, and finite quotient
   entering the extraspecial group.
2. The construction of $Q$, center, elementary abelian quotient, quadratic form,
   and plus-type verification.
3. The Conway quotient and the precise Conway-group properties invoked.
4. The explicit extension $H$, its quotient maps, and its Griess-algebra action.
5. The extra symmetry, its inverse and order, and algebra/form preservation.
6. Each conjugation, intersection, centralizer, and normalizer statement used
   in the global argument.
7. The separate finiteness, order, and simplicity proofs and external references.
8. Correspondence with the historical Monster construction: distinguish a
   verified concrete model from an additional comparison or recognition theorem.
9. VOA facts actually needed in the finite-group proof, and the separate
   generator-lifting and weight-two-generation passages.

Do not assume that every prerequisite is proved internally in FLM. Follow its
references and surface missing proofs as dependencies.

## Candidate supplementary reading

[“Why do the symmetries of the monster vertex algebra form a finite simple group?”](https://arxiv.org/abs/2206.15391)
is a relevant search-result lead for the last milestone. Its text has not been
reviewed or adopted as a proof source. The title alone establishes no theorem
or shortcut for this formalization.

## Review boundary

The first PR contains a coarse roadmap and this checklist. Before creating
formalizable leaf articles, review the chapter scope and coverage contract,
obtain the passages, and compare each intended statement with the source.
Distinguish source theorems, background prerequisites, and project-authored
bridge lemmas.
