# PBiased HCLib

The two-point hypercontractive inequality at bias `p`: for every `ρ ∈ [0, 1]` and
`u, v : ℝ`, the `ρ`-noised second moment is at most the `q = 1 + ρ²` norm.
Holds at `p = 1/2` (`htl_lib_half`); fails for every `p` with `1/2 < p < 1` by the
informal cubic-term argument in the module documentation (formally refuted at
`p = 9/10` in `dtpc_pbiasedHCLib_nine_tenths_false`); at `p = 1` it is equality.
