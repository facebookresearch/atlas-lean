# Validity of the one-sided Fisher exact test

Let `X ~ Bin(n₁, p)` and `Y ~ Bin(n₂, p)`
be independent with a common `p ∈ (0, 1)`. Conditionally on the margin `X + Y = t`, the upper
Fisher exact p-value is valid: `P(fisherUpperPValue ≤ s | X + Y = t) ≤ s` for `s ∈ [0, 1]`.
The bound holds for every nuisance `p`, because the conditional law of `X` does not depend on
it. This is the one-sided (upper) test only.

## Sources

- Lehmann–Romano (2005), §4.5 and Lemma 3.3.1.
