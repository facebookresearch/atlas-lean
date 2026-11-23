# `D` is not Gaussian for a fixed sample size

For `n ≥ 4` genes, integer-valued `S` and
`|π - S / a₁| ≤ β S` almost surely, `D` is almost surely bounded (`abs_tajimaD_le`; at `S = 0`
it takes the junk value `0`), so its law is not `N(m, v)` for any `v ≠ 0`. This is a statement
about one fixed sample; it does not by itself rule out a Gaussian limit in distribution of a
sequence of such samples (see the module docstring).
