# Local L-factor

The local `L`-factor of `χ` at `v`: for an unramified character the
Euler factor `(1 - χ ϖ * N(v) ^ (-s))⁻¹` at the uniformizer
`ϖ = NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v`, and `1` for a ramified
character. This is the analytic `L`-factor at every `s` that is not a pole. At a pole, where
`χ ϖ * N(v) ^ (-s) = 1` (for the trivial character, at `s = 0`), the formula takes Lean's
`0⁻¹ = 0`, so `localLFactorAt` is `0` there instead of a pole.
