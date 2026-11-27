# Solvable terms are those with a head normal form

For every untyped λ-term $t$ the following are equivalent:

1. $t$ is solvable;
2. $t$ is β-convertible to a head normal form;
3. the head reduction of $t$ is finite, that is, it ends in a head normal form.

Moreover $t$ is solvable exactly when $t$ reduces by β- and η-reductions to a head normal form.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Head normal forms and solvable terms](head-normal-forms-and-solvable-terms.md)
- [η-reduction and βη-conversion](../beta-reduction-and-confluence/eta-reduction-and-beta-eta-conversion.md)

## Proof depends on

- [Solvable terms are the terms typable with a non-trivial intersection type](../intersection-types/solvable-terms-are-typable-in-d-omega.md)
- [The standardization theorem](../beta-reduction-and-confluence/standardization-theorem.md)
- [Church–Rosser theorem for βη-reduction](../beta-reduction-and-confluence/church-rosser-theorem-for-beta-eta-reduction.md)

## Expansion

This page becomes ready once:

- Backward η-steps preserve typability with a non-trivial intersection type: if $t \to_\eta t'$ and $t'$ has a non-trivial type in DΩ, so does $t$, after instantiating type variables by arrow types (Lemma 4.29 of Krivine's book; proof prerequisite for the last sentence; not yet stated)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 2, Theorem 2.3 (statement); Chapter 4, Theorem 4.9 (proof through system DΩ) and Theorem 4.32 (the βη form).
