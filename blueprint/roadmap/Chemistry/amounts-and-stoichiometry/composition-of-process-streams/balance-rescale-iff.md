# A species balance is invariant under positive rescaling of all terms

For a factor `0 < α`, [process streams](stream-flow.md) with species flow rates `ṅ_in i` and
`ṅ_out i`, and real vectors `gen` and `acc`, the [species balance](is-balance.md) holds for the
[rescaled streams](rescale.md) with flow rates `α * ṅ_in i` and `α * ṅ_out i`, generation
`α * gen i` and accumulation `α * acc i` if and only if it holds for the original data:

`α * ṅ_in i - α * ṅ_out i + α * gen i = α * acc i` for every `i` exactly when
`ṅ_in i - ṅ_out i + gen i = acc i` for every `i`.

All four terms are scaled by the same factor. Positivity of `α` is needed for the converse: for
`α = 0` every rescaled balance holds (`0 = 0`), whatever the original data.
