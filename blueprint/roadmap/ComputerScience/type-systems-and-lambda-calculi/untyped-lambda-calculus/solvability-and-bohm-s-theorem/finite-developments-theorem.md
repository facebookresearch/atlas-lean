# The finite developments theorem

Let $t$ be an untyped λ-term and $R$ a set of redexes of $t$.

1. There is an integer $N$ such that every development of $(t, R)$ has length at most $N$.
2. Every development of $(t, R)$ extends to a complete development.
3. All complete developments of $(t, R)$ end in the same term.

The theorem is the main step in the proof of the standardization theorem.

## Depends on

- [Residuals and developments](residuals-and-developments.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)

## Proof depends on

- [Strongly normalizing terms are the terms typable in system D](../intersection-types/strongly-normalizing-terms-are-typable-in-d.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 4, Theorem 4.38 (finite developments theorem), proved through Corollary 4.36 (every term of the marked calculus $\Lambda(c)$ is strongly normalizable).
