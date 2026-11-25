# Conv smul right

A `ℤˣ` scalar on the right factor pushes through convolution, reusing
`tensorCochain_smul_right` and the pinned `Cochain.comp_units_smul`/
`Cochain.units_smul_comp`. Degrees stay `m + n` with the same `zero_add`/
`add_zero` transports as `conv`.
