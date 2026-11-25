# Conv smul left

A `ℤˣ` scalar on the left factor pushes through convolution, reusing
`tensorCochain_smul_left` and the pinned `Cochain.comp_units_smul`/
`Cochain.units_smul_comp`. Degrees stay `m + n` with the same `zero_add`/
`add_zero` transports as `conv`.
