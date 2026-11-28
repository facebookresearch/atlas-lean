# Chronological product of a gate sequence

For a monoid `R` and a sequence of gates `U : Fin T → R`, `circuitProd U` is
the chronological product `U (T - 1) * ... * U 1 * U 0`: index `0` is the
first gate applied to the state. For `T = 0` it is `1`.
