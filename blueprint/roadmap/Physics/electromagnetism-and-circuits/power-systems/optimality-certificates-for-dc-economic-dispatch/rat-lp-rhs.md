# Rational right-hand side of the dispatch linear program

For rational `d`, `p_min`, `p_max`, `f_min` and `f_max`, the rational right-hand side is
`(-d, d, 0, 0, p_max, -p_min, f_max, -f_min)`, in the row order of the real
[right-hand side](../dc-economic-dispatch-as-a-linear-program/lp-rhs.md). The rational linear
program that the exact checker assembles from such data casts to the real one built from the cast
data: [matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
