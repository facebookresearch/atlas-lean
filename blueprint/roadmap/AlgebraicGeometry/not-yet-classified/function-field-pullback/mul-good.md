# Admissible multiplier

For an elliptic curve `W`, `n • genericPoint W K` is nonzero and is
not the base change of a point over `K`. This is what `mulPull W K n` needs;
`zsmul_genericPoint_good` proves it when `K` is algebraically closed and `(n : K) ≠ 0`.
