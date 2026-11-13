# Read covering a base of a circular genome

A read of length `L` starting at position `s` of a circular genome of length `G` covers base
`x` when `x` is one of `s, s + 1, …, s + L - 1 (mod G)`, i.e. `(x - s) mod G < L`.
