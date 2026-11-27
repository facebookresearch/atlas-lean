# Closed-form second moments of the Kingman holding times

For natural numbers `k` and `l`, let

`t_{k,l} = 2 / C(k, 2)²` if `k = l`, and `t_{k,l} = 1 / (C(k, 2) C(l, 2))` if `k ≠ l`.

For `k, l ≥ 2` it is the second moment `E[T_k T_l]` of independent holding times `T_k` with the
exponential law of rate `C(k, 2)`
([second moments of the holding times](../kingman-s-coalescent-and-watterson-s-estimator/integral-t-mul-t.md)).
With the convention `0⁻¹ = 0` it is defined for all `k` and `l`: it is `0` when `k < 2` or
`l < 2`, where `C(k, 2) = 0` or `C(l, 2) = 0`.
