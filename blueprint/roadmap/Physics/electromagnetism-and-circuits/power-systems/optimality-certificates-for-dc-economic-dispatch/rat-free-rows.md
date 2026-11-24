# Rational constraint rows on the free variables

For a block of `k` rows with rational generation coefficients `P` (a `k × n_G` matrix) and angle
coefficients `T` (a `k × n_N` matrix), row `i` of the block is `(P_i, T_i)`, acting on the free
variables `(p, θ)`, generation first. The rational objects copy the real ones entrywise, so that the
checker is computable; the [casting lemmas](rat-lp-matrix-map.md) identify them with the real linear
program.
