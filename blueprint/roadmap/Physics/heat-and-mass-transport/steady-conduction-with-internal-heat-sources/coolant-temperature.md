# Integrated coolant temperature along the channel

For real `ṁ`, `cp`, `q₀`, `Lₑ`, `L`, `T_in` and `z`, the integrated coolant temperature is

`T(z) = T_in + q₀Lₑ (sin(πz/Lₑ) + sin(πL/(2Lₑ)))/(π ṁ cp)`.

It is intended for `ṁ > 0`, `cp > 0` and `Lₑ > 0`; with `x/0 = 0` it is the constant `T_in` when
`ṁ cp = 0` or `Lₑ = 0`. For those parameters it
[is a steady coolant profile](is-steady-coolant-profile-coolant-temper.md), and
[every steady coolant profile equals it](eq-coolant-temperature.md) on the heated length.
