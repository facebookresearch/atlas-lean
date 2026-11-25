# Conv add left

Convolution distributes over addition on the left, reusing
`tensorCochain_add_left` and the pinned `Cochain.comp_add`/`Cochain.add_comp`.
Degrees stay `m + n` with the same `zero_add`/`add_zero` transports as `conv`.
