# Splitting the last factor of a coefficient tensor stage

For a commutative semiring R, an R-module M_a and a dependent
family V_(j,a) indexed by Fin(t + 1), this is the R-linear stage splitting
M_a ⊗ (⨂_(j:Fin(t+1)) V_(j,a)) ≅
(M_a ⊗ (⨂_(j:Fin t) V_(j.castSucc,a))) ⊗ V_(Fin.last t,a).
It sends x ⊗ tprod(y) to
(x ⊗ tprod(prefix(y))) ⊗ y_(Fin.last t), with all tensors over R.
