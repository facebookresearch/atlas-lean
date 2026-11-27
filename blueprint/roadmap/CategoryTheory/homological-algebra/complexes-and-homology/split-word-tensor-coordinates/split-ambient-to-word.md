# Ambient tensors map to a chosen coloured coordinate

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). splitAmbientToWord c : A^⊗N →ₗ[k] W_c tensors p or q at each
position according to c.
