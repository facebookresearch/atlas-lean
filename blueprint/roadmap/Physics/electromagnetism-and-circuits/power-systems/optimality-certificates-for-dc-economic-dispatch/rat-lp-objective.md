# Rational objective of the dispatch linear program

For rational costs `c`, the rational objective of the maximized linear program is `-c` on the
positive generation parts, `0` on the positive angle parts, `c` on the negative generation parts and
`0` on the negative angle parts, in the column order of the real
[objective](../dc-economic-dispatch-as-a-linear-program/lp-objective.md). The rational objects copy
the real ones entrywise, so that the checker is computable; the
[casting lemmas](rat-lp-matrix-map.md) identify them with the real linear program.
