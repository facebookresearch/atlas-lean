# Torsion count of `Pic0`

`AbelJacobiCard K F p g` says that `p` is prime and that, for every
`n`, the `p ^ n`-torsion subgroup `AddSubgroup.torsionBy (Pic0 K F) (p ^ n)` has `p ^ (2 * g * n)`
elements. This is the count expected when `F` is the function field of a curve of genus `g` over an
algebraically closed field `K` and `p` is different from the characteristic of `K`. Since
`p ^ (2 * g * n)` is positive for a prime `p`, the condition forces every `p ^ n`-torsion subgroup
to be finite (`Nat.card` is `0` on an infinite type). Primality is part of the condition because
the count is degenerate otherwise: for `p = 1` it holds for every `g`, and for `p = 0` and `g ≥ 1`
it only says that `Pic0 K F` is infinite.
