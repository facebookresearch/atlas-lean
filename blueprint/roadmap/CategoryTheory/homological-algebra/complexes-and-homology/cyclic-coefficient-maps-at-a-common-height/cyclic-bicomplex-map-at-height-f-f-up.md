# The lifted cyclic cell map has the coefficientwise tensor value

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For p, q : ℕ and x : A ⊗[k] TensorPower k q A, the cell (p,q) map
sends ULift.up x to ULift.up (TensorPower.consLevelMap f q x). Thus f acts on the
distinguished coefficient and each of the q tensor factors.
