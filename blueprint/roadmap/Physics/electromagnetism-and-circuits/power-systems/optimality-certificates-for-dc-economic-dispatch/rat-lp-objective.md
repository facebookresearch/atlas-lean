# Rational objective of the dispatch linear program

For rational costs `c`, the rational objective of the maximized linear program is `-c` on the
positive generation parts, `0` on the positive angle parts, `c` on the negative generation parts and
`0` on the negative angle parts, in the column order of the real
[objective](../dc-economic-dispatch-as-a-linear-program/lp-objective.md). The rational linear
program that the exact checker assembles from such data casts to the real one built from the cast
data: [matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
