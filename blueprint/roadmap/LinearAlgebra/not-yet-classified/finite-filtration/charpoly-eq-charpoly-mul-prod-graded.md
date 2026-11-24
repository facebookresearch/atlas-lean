# Charpoly eq charpoly mul prod graded

The characteristic polynomial on the final stage of a finite invariant
filtration is the characteristic polynomial on the initial stage times the
product of the characteristic polynomials on all successive graded
quotients.  This is the characteristic-polynomial analogue of
`LinearMap.det_eq_det_mul_prod_graded`, with the same interface: each
`step i` identifies stage `i` with an invariant submodule of stage `i+1`.
