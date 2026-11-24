# Steady coolant temperature profile on the heated length

For real `ṁ`, `cp`, `q₀`, `Lₑ`, `L` and `T_in`, a function `T : ℝ → ℝ` is a steady coolant profile
if `T(-L/2) = T_in` and, at every `z` with `-L/2 ≤ z ≤ L/2`, `T` is differentiable at `z` and

`ṁ cp T′(z) = q′(z)`,

with the [linear power](cosine-linear-power.md) `q′(z) = q₀ cos(πz/Lₑ)`. This is the steady energy
balance of a thin section of the channel with mass flow `ṁ` and specific heat `cp`, with no shaft
work or storage, enthalpy `cp T`, and kinetic and potential changes neglected.
