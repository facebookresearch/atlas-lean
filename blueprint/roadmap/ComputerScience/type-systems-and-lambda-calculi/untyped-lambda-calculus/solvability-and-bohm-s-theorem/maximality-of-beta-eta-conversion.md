# Maximality of βη-conversion

Let $\sim$ be an equivalence relation on untyped λ-terms that contains β-conversion and is compatible with application and abstraction: $t \sim t'$
implies $t\, u \sim t'\, u$ and $\lambda x.\, t \sim \lambda x.\, t'$ for all terms $t, t', u$ and variables $x$. If $\sim$ identifies two β-normalizable terms that are not
βη-convertible, then $\sim$ identifies all terms.

So no consistent λ-theory identifies two distinct βη-normal forms: βη-conversion is maximal among consistent extensions of β-conversion on
normalizable terms.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [η-reduction and βη-conversion](../beta-reduction-and-confluence/eta-reduction-and-beta-eta-conversion.md)

## Proof depends on

- [Böhm's theorem](bohm-s-theorem.md)
- [Church–Rosser theorem for βη-reduction](../beta-reduction-and-confluence/church-rosser-theorem-for-beta-eta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 5, Corollary 5.4 and the remark preceding it; Corollary 5.7 gives the variant for relations compatible with substitution.
