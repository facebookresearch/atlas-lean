# The cyclic homology map commutes with the lift comparison

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For n : ℕ and lift comparisons e_A, e_B, cyclicHomologyMapAtHeight f n
≫ e_B.hom = e_A.hom ≫ homologyMap (cyclicTotalMapAtHeight f) n. Both sides map the lifted base
homology of A to the homology of B's lifted total.
