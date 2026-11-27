# The continuous existential is not definable in PCF with the parallel conditional

Let $\exists \in D_{(\iota \to o) \to o}$ be the continuous function with $\exists(f) = \mathit{ff}$ if $f(\bot) = \mathit{ff}$, $\exists(f) = \mathit{tt}$ if $f(n) = \mathit{tt}$ for some
$n \ge 0$, and $\exists(f) = \bot$ otherwise, the best continuous approximation to the existential quantifier over the natural numbers. Then $\exists$ is a
[computable element](computable-elements-of-the-pcf-model.md), but it is not the denotation of any closed term of
[PCF with the parallel conditional](pcf-with-the-parallel-conditional.md). So definability in $\mathcal{L}_{PA}$ is strictly weaker than computability.

The proof shows by induction on $k$ that a term $E$ of ground type with one free variable $\alpha : \iota \to o$, whose instances at a term defining
$\bot \Rightarrow \mathit{ff}$ and at terms $T_n$ defining $n \Rightarrow \mathit{tt}$ have different, non-$\bot$ denotations for infinitely many $n$, cannot terminate in fewer than $k$
steps at the first instance. A closed definition $M$ of $\exists$ would make $E = M\, \alpha$ such a term; its instance at $F$ is $M F$, which would then not terminate although it
denotes $\mathit{ff}$, contradicting computational adequacy for this language.

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)
- [Computable elements of the PCF model](computable-elements-of-the-pcf-model.md)

## Expansion

This page becomes ready once:

- Computational adequacy for PCF with the parallel conditional at both ground types: a closed term of ground type whose denotation is a constant $c$ reduces to $c$ (the analogue of Theorem 3.1 of the source below for $\mathcal{L}_{PA}$; proof prerequisite; not yet stated as a page)

## Background

- [Parallel or is not definable in PCF](parallel-or-is-not-definable-in-pcf.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 5, the definition of $\exists$ and the proof that it is not $\mathcal{L}_{PA}$-definable on pages 250–251, which ends by appeal to the analogue of Theorem 3.1 for $\mathcal{L}_{PA}$.
