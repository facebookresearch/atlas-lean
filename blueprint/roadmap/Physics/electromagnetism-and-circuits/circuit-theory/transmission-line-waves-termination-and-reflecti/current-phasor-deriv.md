# Phasor telegrapher equation for the current

Let `L > 0` and `C > 0` be the inductance and capacitance per unit length, let `ω` be real, and let
`β = ω √(L C)` be the [phase constant](phase-constant.md) and `Z₀ = √(L / C)` the
[characteristic impedance](characteristic-impedance.md). For complex amplitudes `A₊` and `A₋`,
consider the [voltage phasor](voltage-phasor.md) `V(x) = A₊ e^{−iβx} + A₋ e^{iβx}` and the
[current phasor](current-phasor.md) `I(x) = (A₊ e^{−iβx} − A₋ e^{iβx}) / Z₀`. Then at every position
`x`

`I'(x) = −iωC V(x)`.
