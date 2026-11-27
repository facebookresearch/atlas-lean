# Statman's theorem on equality of typed terms

Deciding whether two Church-style simply typed λ-terms $M$ and $N$ of the same type are β-convertible is of non-elementary complexity, where
$\exp_0(n) = n$ and $\exp_{k+1}(n) = 2^{\exp_k(n)}$: for every decision procedure and every fixed $r$ there are infinitely many $n$ for which some input of
size $n$ takes the procedure more than $\exp_r(n)$ steps. Equivalently, no decision procedure runs within $\exp_r(n)$ steps on all inputs of size $n$ for all
$n$, for any fixed $r$.

Comparing normal forms decides the problem, since simply typed terms normalize; the theorem says the cost of normalization cannot be avoided.

## Depends on

- [Intrinsically typed terms of the simply typed lambda calculus](../tm.md)

## Expansion

This page becomes ready once:

- Full β-reduction and β-conversion of simply typed terms (statement prerequisite; not yet stated as a page)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 6.7, Theorem 6.7.1 (Statman) and the paragraph before it.
