# Upper Unipotent mixed Swap chev

Mixed adjacent swap: for `a < b < n`, `x b n v * x a b u` equals
`x a n (-(u * v)) * (x a b u * x b n v)` in head-left collected order, with
correction coefficient `-(u * v)` in ordinary `u * v` order. Proved from
accepted `x_chev` via the repository commutator convention
`⁅x, y⁆ = x * y * x⁻¹ * y⁻¹` plus ordinary group algebra, then accepted
`x_neg` for the sign. Purpose: atomic mixed collection step. Nonclaims: no
evaluator multiplication/inversion closure, ordered normal form, uniqueness,
`toStableE` injectivity, TWT, kernel generation, or Matsumoto theorem.
