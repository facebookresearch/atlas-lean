---
article_id: af_7372c3e9c47424c5292cd1c5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.catalan_odd_terms_shift_unique
---

# Catalan Odd Terms Shift

The shift `α = 3/4` is the unique value for which the asymptotic expansion of
the Catalan numbers in powers of `1/(n+α)` has vanishing odd-indexed
coefficients: `Catalan(n) * √π * (n+α)^{3/2} / 4^n` admits an asymptotic
expansion `Σ a_k (n+α)^{-k}` with `a_{2k+1} = 0` for all `k` if and only if
`α = 3/4`.

The source's wording "contains only odd terms" refers to the odd-indexed
coefficients vanishing: its displayed `α = 3/4` series (lines 546–555) has
only even powers, and the proof obtains `α = 3/4` by zeroing the odd
coefficient `c_1`. The `α = 3/4` coefficient recurrence is equation
calpha-34 (lines 443–445).

Proof: The reverse implication exponentiates the all-orders logarithmic
expansion from `CatalanAsymptoticExpansion.lean` and uses Bernoulli reflection
to eliminate odd powers. The first logarithmic coefficient gives uniqueness,
following Elezović.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Tendsto pow mul log catalan sub bernoulli sum](catalan-asymptotic-expansion/tendsto-pow-mul-log-catalan-sub-bernoull.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Asymptotics.CatalanOddTermsShift](../../../../../sources/v2/MathlibExt.md)
- Neven Elezović, "Asymptotic Expansions of Central Binomial Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014), Article 14.2.1, Corollary, lines 568–578, https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex
