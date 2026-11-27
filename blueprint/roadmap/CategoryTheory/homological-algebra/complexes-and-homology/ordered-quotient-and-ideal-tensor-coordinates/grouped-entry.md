# The grouped tensor entries use quotient modules first and ideal modules second

Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). In the sum index Fin(#true) ⊕ Fin(#false), groupedEntry takes the
module A/I on the left group and I on the right group.
