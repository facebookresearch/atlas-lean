# Validity of the exact conditional Poisson test

Let `X ~ Po(s₁ r)` and `Y ~ Po(s₂ r)` be
independent counts of one gene in two conditions with library sizes `s₁, s₂` (`s₁ + s₂ > 0`) and
a common rate `r ≥ 0` (the null hypothesis of equal expression). Then the exact p-value
`countExactPValue s₁ s₂ X Y` is valid: `P(p ≤ t) ≤ t` for every `t ∈ [0, 1]`, whatever `r`
(including `r = 0`, a gene that is never expressed).

The proof averages the conditional guarantee over the total `X + Y`. This is a statement about
the Poisson null only: under negative-binomial overdispersion the conditional law of `X` given
`X + Y` is no longer binomial and no calibration is asserted.

## Sources

- Przyborowski–Wileński (1940); Lehmann–Romano (2005), §4.5 and Lemma 3.3.1.
