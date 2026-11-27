# Fixed point theorem for the λ-calculus

For every untyped λ-term $F$ there is a term $X$ with $F\, X =_\beta X$. Uniformly, the
[paradoxical combinator $Y$](../../../programming-language-semantics/models-of-the-untyped-lambda-calculus/y.md) satisfies $F\, (Y\, F) =_\beta Y\, F$ for every $F$. Consequently, for every term $M$ there is a term $F$ with $F =_\beta M[f := F]$, namely $F = Y\, (\lambda f.\, M)$: recursive
definitions can be solved up to β-conversion. Turing's combinator $Z = A\, A$ with $A = \lambda a\, f.\, f\, (a\, a\, f)$ even satisfies $Z\, F \twoheadrightarrow_\beta F\, (Z\, F)$, by head reduction.

## Depends on

- [β-reduction](beta-reduction.md)
- [The paradoxical combinator $Y$](../../../programming-language-semantics/models-of-the-untyped-lambda-calculus/y.md)
- [Head normal forms and solvable terms](../solvability-and-bohm-s-theorem/head-normal-forms-and-solvable-terms.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 1.5.10 (fixed point theorem) and Corollary 1.5.11.
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 2, Section 3, Propositions 2.9 and 2.10 (the terms $Y$ and $Z = A\, A$ with $A = \lambda a\, f.\, f\, (a\, a\, f)$).
