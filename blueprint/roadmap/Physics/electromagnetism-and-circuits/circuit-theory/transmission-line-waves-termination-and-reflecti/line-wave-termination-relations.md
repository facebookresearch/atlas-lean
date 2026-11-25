# Wave relations and load reflection on a lossless line

Let `L > 0`, `C > 0`, `ω > 0` and `Z₀ > 0`, with `β = ω √(L C)` the
[phase constant](phase-constant.md) and `Z₀ = √(L / C)` the
[characteristic impedance](characteristic-impedance.md), and let `A₊`, `A₋` and `Z_L` be complex.
Then:

- the [wave speed](wave-speed.md) `v` satisfies `v √(L C) = 1`, and `Z₀² = L / C`;
- at every position `x`, the [voltage phasor](voltage-phasor.md) `V(x) = A₊ e^{−iβx} + A₋ e^{iβx}`
  and the [current phasor](current-phasor.md) `I(x) = (A₊ e^{−iβx} − A₋ e^{iβx}) / Z₀` satisfy
  `V'(x) = −iωL I(x)` and `I'(x) = −iωC V(x)`;
- for all complex `V` and `I` with `V = A₊ + A₋`, `I = (A₊ − A₋) / Z₀` and `V = Z_L I`,
  `(Z_L + Z₀) A₋ = (Z_L − Z₀) A₊`, and if moreover `A₊ ≠ 0`, then `Z_L + Z₀ ≠ 0` and
  `A₋ / A₊ = (Z_L − Z₀) / (Z_L + Z₀)`.
