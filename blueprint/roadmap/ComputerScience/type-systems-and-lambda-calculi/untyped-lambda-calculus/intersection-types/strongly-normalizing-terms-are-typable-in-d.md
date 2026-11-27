# Strongly normalizing terms are the terms typable in system D

An untyped λ-term is strongly β-normalizing, that is, it has no infinite β-reduction sequence, if and only if it is typable in
[system D](intersection-type-system-d.md): $\Gamma \vdash_D t : A$ for some context $\Gamma$ and type $A$.

That every strongly normalizing term is typable is proved by induction on the sum of the lengths of all reduction paths of the term, which is finite
because it is strongly normalizing. That every typable term is strongly normalizing is proved by reducibility, with saturated sets of strongly
normalizing terms.

## Depends on

- [The intersection type system D](intersection-type-system-d.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

- [Adequacy lemma for system D](adequacy-lemma-for-system-d.md)
- [β-normal terms are typable in system D](normal-terms-are-typable-in-system-d.md)
- [Typing substituted terms with intersections](typing-substituted-terms-with-intersections.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 3, Theorem 3.20 (strong normalization theorem) and Proposition 3.18; Chapter 4, Theorem 4.17 and Corollary 4.18.
