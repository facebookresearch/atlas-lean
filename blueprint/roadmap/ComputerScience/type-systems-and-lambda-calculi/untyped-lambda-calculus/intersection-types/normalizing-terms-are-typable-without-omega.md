# Normalizing terms are the terms typable without Ω

For every untyped λ-term $t$ the following are equivalent:

1. $t$ is β-normalizable;
2. leftmost β-reduction of $t$ terminates;
3. $\Gamma \vdash_{D\Omega} t : A$ for some type $A$ and context $\Gamma$ such that neither $A$ nor any type in $\Gamma$ contains $\Omega$;
4. $\Gamma \vdash_{D\Omega} t : A$ for some type $A$ with no positive occurrence of $\Omega$ and some context $\Gamma$ with no negative occurrence of $\Omega$.

In particular leftmost reduction is a normalizing strategy: it reaches the β-normal form of every normalizable term.

## Depends on

- [The intersection type system DΩ](intersection-type-system-d-omega.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

- [Subject reduction and subject expansion for intersection types](subject-reduction-and-expansion-for.md)
- [Saturated sets and the adequacy lemma for DΩ](saturated-sets-and-the-adequacy-lemma-for-d-omega.md)
- [β-normal terms are typable in system D](normal-terms-are-typable-in-system-d.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 3, Theorem 3.10 (normalization theorem) and Corollary 3.11; Chapter 4, Theorem 4.13 (the four conditions are equivalent).
