# Strong normalization of λΔ via a CPS translation

For the [CPS translation](a-cps-translation-of-lambda-delta.md) $t$ of λΔ-terms:

1. if $M =_{\beta\Delta} N$ then $t(M) =_\beta t(N)$;
2. if $M$ has an infinite $\beta\Delta$-reduction sequence, then so does $t(M)$ for β.

Consequently $\to_{\beta\Delta}$ is strongly normalizing on typable terms of the simply typed [λΔ-calculus](the-lambda-delta-calculus.md), since $t$ maps them to typable simply
typed λ-terms.

## Depends on

- [A CPS translation of λΔ](a-cps-translation-of-lambda-delta.md)
- [Simple type assignment à la Curry](../../simply-typed-lambda-calculus/decision-problems-for-simple-types/simple-type-assignment-a-la-curry.md)
- [β-reduction](../../untyped-lambda-calculus/beta-reduction-and-confluence/beta-reduction.md)

## Expansion

This page becomes ready once:

- Strong normalization of full β-reduction for the simply typed λ-calculus, as a page (proof prerequisite; not yet stated as a page)
- A proof of part 2, which the lecture notes below state without proof, checked against a source that proves it (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 8.6, Propositions 8.6.5 and 8.6.6 and Corollary 8.6.7.
