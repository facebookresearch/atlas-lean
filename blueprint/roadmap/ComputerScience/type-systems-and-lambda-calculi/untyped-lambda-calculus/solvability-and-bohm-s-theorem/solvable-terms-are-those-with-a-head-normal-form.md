# Solvable terms are those with a head normal form

For every untyped λ-term $t$ the following are equivalent:

1. $t$ is solvable;
2. $t$ is β-convertible to a head normal form;
3. the head reduction of $t$ is finite, that is, it ends in a head normal form.

Moreover $t$ is solvable exactly when $t$ reduces by β- and η-reductions to a head normal form.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Head normal forms and solvable terms](head-normal-forms-and-solvable-terms.md)

## Proof depends on

- [Solvable terms are the terms typable with a non-trivial intersection type](../intersection-types/solvable-terms-are-typable-in-d-omega.md)

## Expansion

This page becomes ready once:

- βη-conversion $\simeq_{\beta\eta}$ of untyped λ-terms and its Church–Rosser property (statement prerequisite; not yet stated as a page)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 2, Theorem 2.3 (statement); Chapter 4, Theorem 4.9 (proof through system DΩ) and Theorem 4.32 (the βη form).
