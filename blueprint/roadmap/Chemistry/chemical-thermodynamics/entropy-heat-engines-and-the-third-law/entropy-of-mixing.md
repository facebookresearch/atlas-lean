# Ideal entropy of mixing

The ideal entropy of mixing `ΔS_mix = n * R * H(x)` for mole fractions `x`, where
`H(x) = -∑ i, x i * log (x i)` is the [Shannon
entropy](../canonical-ensemble-of-a-finite-system/shannon-entropy.md). Model input: ideal mixing, as
for ideal gases or an ideal solution (random mixing, no excess entropy). A nonideal mixture adds an
excess entropy `S^E`, so this is not the entropy of mixing of a general mixture. By the convention
`log 0 = 0`, a component with `x i = 0` contributes `0 * log 0 = 0`, the continuous extension of
`x * log x` and so the correct value. Domain: mole fractions (`0 ≤ x i`, `∑ i, x i = 1`); a negative
entry gives `log (-x) = log x`, and the value is then not an entropy (it can be negative).
Gibbs-paradox remark: mixing identical gases gives zero only because they count as one component;
the formula does not resolve the paradox, which needs indistinguishability.
