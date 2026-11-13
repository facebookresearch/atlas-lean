# Truncated second moment asymptotic for regularly varying tails

The corrected truncated-second-moment asymptotic: for a probability measure
on `ℝ` with regularly varying combined tail of index `-α`, `0 < α < 2`, the
ratio `(∫ y in Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x)` tends to
`α / (2 - α)`.

Correction: `v1/Atlas/TheoryOfProbability/code/RegularVariation.lean` states
this with the constant `2 / (2 - α)`, which is wrong; the Pareto tail gives
`α / (2 - α)` (see the test file).
