# Coeff Hecke T

The coefficient formula of `heckeT k p`: the `n`-th coefficient is
`a (n * p) + p ^ (k - 1) * a (n / p)` when `p ∣ n`, and `a (n * p)` otherwise. For `p ≠ 0`, this
is how `heckeT k p` acts on the `q`-expansion coefficients `a` of a modular form for a group with
`1` as a strict period (`ModularFormClass.qCoeff_heckeT`); at `p = 0` it is not, as
`heckeT k 0 f = f`.
