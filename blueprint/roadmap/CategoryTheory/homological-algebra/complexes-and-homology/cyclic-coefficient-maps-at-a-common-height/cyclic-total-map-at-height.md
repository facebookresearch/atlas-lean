# Totalization maps the common-height cyclic bicomplex morphism

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. cyclicTotalMapAtHeight f is HomologicalComplex₂.total.map of
cyclicBicomplexMapAtHeight f, with total shape down ℕ.
