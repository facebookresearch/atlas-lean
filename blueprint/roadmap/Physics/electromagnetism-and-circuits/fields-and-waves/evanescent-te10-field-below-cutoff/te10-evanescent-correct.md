# Properties of the evanescent TE10 field below cutoff

Let `c > 0` be the speed of light. Let the guide widths be `a > 0` and `b > 0`, `E₀ ≠ 0`, and
`0 < ω < c k_c`, strictly below cutoff, with the [cutoff wavenumber](cutoff-wavenumber.md)
`k_c = π/a`. Let the [decay rate](decay-rate.md) `κ = √(k_c² - ω²/c²)`. Then:

- `κ > 0` and `κ² = k_c² - ω²/c²`;
- the [evanescent electric field](evanescent-electric-field.md) and the
  [evanescent magnetic field](evanescent-magnetic-field.md) with amplitude `E₀`, frequency `ω` and
  rate `κ` satisfy the [source-free vacuum Maxwell equations](../separable-vacuum-maxwell-fields/source-free-vacuum-maxwell.md),
  and at every time the [PEC trace conditions](../te10-mode-of-a-rectangular-waveguide/rectangular-guide-pectraces.md) on the four
  side walls;
- the electric field is not identically zero;
- on the half-guide `z ≥ 0`, every component satisfies `|E_i| ≤ |E₀| e^{-κz}` and
  `|B_i| ≤ ((κ + k_c)|E₀|/ω) e^{-κz}`.
