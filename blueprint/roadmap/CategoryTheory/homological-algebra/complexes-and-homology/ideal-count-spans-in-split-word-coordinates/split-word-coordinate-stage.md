# The coordinate stage is supported on enough ideal positions

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q.
splitWordCoordinateStage N r is the submodule of Π c, W_c consisting of families x with x_c =
0 whenever c has fewer than r false positions.
