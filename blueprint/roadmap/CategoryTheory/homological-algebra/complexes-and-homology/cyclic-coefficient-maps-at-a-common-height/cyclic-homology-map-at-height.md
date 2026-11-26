# The total map induces a map between lifted cyclic homology objects

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For n : ℕ, cyclicHomologyMapAtHeight maps U_H(HC_n(A)) to
U_H(HC_n(B)). If e_A and e_B are the lift-to-total-homology isomorphisms, it is e_A.hom ≫
H_n(cyclicTotalMapAtHeight f) ≫ e_B.inv.
