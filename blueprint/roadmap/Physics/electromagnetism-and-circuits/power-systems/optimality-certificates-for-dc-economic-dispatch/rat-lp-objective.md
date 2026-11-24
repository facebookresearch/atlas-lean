# Rational objective of the dispatch linear program

For rational costs `c`, the rational objective of the maximized linear program is `-c` on the
positive generation parts, `0` on the positive angle parts, `c` on the negative generation parts and
`0` on the negative angle parts, in the column order of the real
[objective](../dc-economic-dispatch-as-a-linear-program/lp-objective.md). Its entries are given by
the same formula as for the real linear program, over the rationals, so that the checker is an exact
finite test. The cast of the assembled rational program is the real one:
[matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
