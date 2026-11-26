# The grouped ideal tuple reads the false entries in increasing order

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For N : ℕ and c : Fin N → Bool, let Q_c be the finite set of true
positions and I_c the set of false positions, with the order inherited from Fin N. For typed
entries a_i : E_(c i), idealEntries c a takes the entries at idealPositionOrder c, identified
with I through entryOrderEquiv.
