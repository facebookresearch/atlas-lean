# Inhabitation in λP is undecidable

It is undecidable, given a context $\Gamma$ and a type $\tau$ of [λP](the-calculus-lambda-p.md), whether some term $M$ satisfies $\Gamma \vdash M : \tau$.

The fragment of first-order intuitionistic logic with $\forall$ and $\to$ as the only connectives and no function symbols embeds in λP, with formulas as types and
proofs as terms, and λP is conservative over this fragment: a formula of the fragment is provable exactly when its type is inhabited. Provability in this
fragment is already undecidable, so inhabitation in λP is undecidable.

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)

## Expansion

This page becomes ready once:

- Undecidability of the fragment of first-order intuitionistic logic with $\forall$ and $\to$ only and no function symbols (proof prerequisite; not yet stated)
- Conservativity of λP over its first-order logic fragment, or the direct proof of M. Bezem and J. Springintveld, *Journal of Functional Programming* 6(5), 1996, checked (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 10.6, Example 10.6.1, Theorem 10.6.2 and the paragraph before it; Corollary 9.3.8 and the paragraph after it (undecidability already for the fragment with $\forall$ and $\to$ and no function symbols).
