# Rational right-hand side of the dispatch linear program

For rational `d`, `p_min`, `p_max`, `f_min` and `f_max`, the rational right-hand side is
`(-d, d, 0, 0, p_max, -p_min, f_max, -f_min)`, in the row order of the real
[right-hand side](../dc-economic-dispatch-as-a-linear-program/lp-rhs.md). The rational objects copy
the real ones entrywise, so that the checker is computable; the
[casting lemmas](rat-lp-matrix-map.md) identify them with the real linear program.
