# Strongly normalizing terms are the terms typable in system D

An untyped λ-term is strongly β-normalizing, that is, it has no infinite β-reduction sequence, if and only if it is typable in
[system D](intersection-type-system-d.md): $\Gamma \vdash_D t : A$ for some context $\Gamma$ and type $A$.

The forward direction is proved by reducibility with saturated sets of strongly normalizing terms; the converse by induction on the sum of
the lengths of all reduction paths of a strongly normalizing term, which is finite.

## Depends on

- [The intersection type system D](intersection-type-system-d.md)

## Expansion

This page becomes ready once:

- One-step β-reduction of untyped λ-terms as a relation of its own, with its reflexive–transitive closure (statement prerequisite; not yet stated as a page)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 3, Theorem 3.20 (strong normalization theorem) and Proposition 3.18; Chapter 4, Theorem 4.17 and Corollary 4.18.
