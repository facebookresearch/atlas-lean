# Inhabitation in λP is undecidable

It is undecidable, given a context $\Gamma$ and a type $\tau$ of [λP](the-calculus-lambda-p.md), whether some term $M$ satisfies $\Gamma \vdash M : \tau$.

First-order intuitionistic logic embeds in λP, with formulas as types and proofs as terms, and λP is conservative over this fragment; since provability
in first-order intuitionistic logic is undecidable, so is inhabitation in λP.

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)

## Expansion

This page becomes ready once:

- Undecidability of first-order intuitionistic logic (proof prerequisite; not yet stated)
- Conservativity of λP over its first-order logic fragment, or the direct proof of M. Bezem and J. Springintveld, *Journal of Functional Programming* 6(5), 1996, checked (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 10.6, Example 10.6.1, Theorem 10.6.2 and the paragraph before it; Corollary 9.3.8 (first-order intuitionistic logic is undecidable).
