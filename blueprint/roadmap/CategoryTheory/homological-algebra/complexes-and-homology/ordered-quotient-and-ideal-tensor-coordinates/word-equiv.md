# A coloured word is equivalent to quotient tensors followed by ideal tensors

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). wordEquiv c : W_c ≃ₗ[k] TensorPower k (#true) (A/I) ⊗[k]
TensorPower k (#false) I first reindexes by positionOrderEquiv, identifies the entry modules
and separates the two tensor groups.
