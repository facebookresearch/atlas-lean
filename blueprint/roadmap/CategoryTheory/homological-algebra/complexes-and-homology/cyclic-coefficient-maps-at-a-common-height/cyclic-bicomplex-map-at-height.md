# An algebra map gives a cyclic bicomplex map at the common universe

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. cyclicBicomplexMapAtHeight maps the degreewise lifted cyclic bicomplex
of A to that of B. It is the further lift of cyclicBicomplexMap f, conjugated by the
repeated-lift flattening isomorphisms.
