# A merge

The logarithmic amortized bound for `merge` (`a_merge`). The
bound sums the logarithmic spine bounds for the two inputs and the
output (`amor_le_real`); it assumes no worst-case logarithmic height.
`T_merge` is the recursive-equation count, as above.
Isabelle writes the logarithm as `log 2 ((size1 t1 + size1 t2 : ℕ) : ℝ)`;
`size1_add_cast` below states that this equals the real sum
`size1 t1 + size1 t2` used here.
