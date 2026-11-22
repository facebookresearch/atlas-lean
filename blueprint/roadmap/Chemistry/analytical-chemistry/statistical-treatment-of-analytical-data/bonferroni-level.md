# Bonferroni Level

Bonferroni-adjusted level `α/m`: each of `m` p-values is compared with `α/m`, meaningful for
`m ≥ 1` (at `m = 0` Lean's division returns `0`). It is the threshold of the canonical procedure
`MultipleTesting.bonferroniRejections` (`mem_bonferroniRejections_iff`), whose family-wise error
control is proved there.
