# Ideal entropy of mixing

The ideal entropy of mixing `ΔS_mix = n * R * H(x)` for mole fractions `x : ι → ℝ`, where
`H(x) = -∑ i, x i * log (x i)` is the Shannon entropy
`Chemistry.FiniteEnsembles.shannonEntropy`. Model input: ideal mixing, as for ideal gases or an
ideal solution (random mixing, no excess entropy). A nonideal mixture adds an excess entropy
`S^E` that is not modeled here, so this is not the entropy of mixing of a general mixture.
With Mathlib's convention `Real.log 0 = 0`, a component with `x i = 0` contributes
`0 * log 0 = 0` automatically, the continuous extension of `x * log x` and so the correct value.
Domain: mole fractions (`0 ≤ x i`, `∑ i, x i = 1`), which `entropyOfMixing_nonneg` and
`entropyOfMixing_eq_zero_iff` assume; a negative entry meets Lean's
`Real.log (-x) = Real.log x`, and the value is then not an entropy (it can be negative).
Gibbs-paradox remark: mixing identical gases gives zero here only because they are counted as
one component; the identical-gas resolution (indistinguishability) is not
claimed.
