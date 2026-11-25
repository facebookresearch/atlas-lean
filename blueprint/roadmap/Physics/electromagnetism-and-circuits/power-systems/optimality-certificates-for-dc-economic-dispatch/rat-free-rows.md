# Rational constraint rows on the free variables

For a block of `k` rows with rational generation coefficients `P` (a `k × n_G` matrix) and angle
coefficients `T` (a `k × n_N` matrix), row `i` of the block is `(P_i, T_i)`, acting on the free
variables `(p, θ)`, generation first. Its entries are given by the same formula as for the real
linear program, over the rationals, so that the checker is an exact finite test. The cast of the
assembled rational program is the real one: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
