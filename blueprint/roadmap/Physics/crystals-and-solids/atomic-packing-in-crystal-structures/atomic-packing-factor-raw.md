# Atomic Packing Factor Raw

Raw packing-factor expression `n * ((4/3) π R³) / Vc` for `n` atoms of
radius `R` in a cell of volume `Vc`, on arbitrary reals `R` and `Vc`. Lean's
division is total, so this is `0` for `Vc = 0`; it is a packing factor only for
`0 < R` and `0 < Vc`, the domain that `atomicPackingFactor` enforces.
