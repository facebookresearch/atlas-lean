# Conv add right

Convolution distributes over addition on the right, reusing
`tensorCochain_add_right` and the pinned `Cochain.comp_add`/`Cochain.add_comp`.
Degrees stay `m + n` with the same `zero_add`/`add_zero` transports as `conv`.
