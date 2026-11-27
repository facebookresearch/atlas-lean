# The coefficient word projection fixes the arbitrary coefficient factor

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. coefficientSplitAmbientToWord c : V
⊗[k] A^⊗N →ₗ[k] V ⊗[k] W_c is P_c^V, applying the ideal or quotient projections only to the
word factors.
