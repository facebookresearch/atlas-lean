# The basic reproduction ratio `R₀`

The per-generation growth factor of a bounded real
operator `K`, an alias for Mathlib's Gelfand radius `gelfandRadius K`: the limit of
`‖K^m‖^(1/m)` (`tendsto_gelfandRadius`), which is also `inf_{m ≥ 1} ‖K^m‖^(1/m)` and equals the
spectral radius of the complexification of `K`. It is the basic reproduction ratio `R₀ = r(K)` of
Diekmann, Heesterbeek and Metz (1990, Eq. (2.2)).
