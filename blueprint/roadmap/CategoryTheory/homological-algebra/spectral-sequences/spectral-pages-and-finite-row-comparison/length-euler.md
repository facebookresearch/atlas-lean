# The finite-rectangle page length Euler sum

For a homological spectral sequence `E` of modules over a commutative ring
`R` and page `r ≥ 1`, the integer Euler sum over `0 ≤ p ≤ m`, `0 ≤ q ≤ n`,
with summand `(-1)^(p+q) * (Module.length R ((E.page r hr).X (p,q))).toNat`.
The definition uses `Module.length.toNat`; the invariance theorems require
finite module lengths and vanishing outside this rectangle.
