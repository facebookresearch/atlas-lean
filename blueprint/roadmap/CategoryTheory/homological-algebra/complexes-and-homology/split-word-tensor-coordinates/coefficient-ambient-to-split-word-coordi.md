# The coefficient coordinate map collects every coloured projection

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c.
coefficientAmbientToSplitWordCoordinates maps x : V ⊗ A^⊗N to the family colour ↦
P_colour^V(x).
