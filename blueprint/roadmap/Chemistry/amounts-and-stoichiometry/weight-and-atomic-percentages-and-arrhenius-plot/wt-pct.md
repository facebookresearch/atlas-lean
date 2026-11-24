# Weight percent of a component

For a finite set `ι` of components, molar masses `M : ι → ℝ` and amounts (or mole fractions)
`x : ι → ℝ`, the weight percent of component `i` is `100 x_i M_i / ∑_j x_j M_j`, `100` times the
[mass fraction](../amount-of-substance-and-molar-mass/mass-fraction.md). With the convention
`x / 0 = 0` it is `0` for every component when `∑_j x_j M_j = 0`. For positive molar masses and
nonnegative amounts, not all zero, this is the weight percent in the usual sense; for other real
inputs the formula still applies but is not a percentage.
