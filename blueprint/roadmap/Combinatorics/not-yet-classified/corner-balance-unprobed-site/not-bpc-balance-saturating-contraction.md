# Not bpc Balance Saturating Contraction

`bpc_BalanceSaturatingContraction` is false: saturated sets contract by the saturated
property itself, and unsaturated sets contract by removing a site outside the footprint
(`bpc_contraction_of_not_saturating`), so the saturated property would imply
`BalancePreservingContraction`, which is false.
