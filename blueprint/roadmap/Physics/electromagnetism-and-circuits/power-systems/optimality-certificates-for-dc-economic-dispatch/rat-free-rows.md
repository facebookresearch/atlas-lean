# Rational constraint rows on the free variables

For a block of `k` rows with rational generation coefficients `P` (a `k × n_G` matrix) and angle
coefficients `T` (a `k × n_N` matrix), row `i` of the block is `(P_i, T_i)`, acting on the free
variables `(p, θ)`, generation first. The rational linear program that the exact checker assembles
from such data casts to the real one built from the cast data: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
