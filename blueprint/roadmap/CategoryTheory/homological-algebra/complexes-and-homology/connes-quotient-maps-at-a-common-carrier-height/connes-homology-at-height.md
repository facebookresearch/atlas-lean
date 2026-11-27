# The Connes quotient at height h has homology in every degree

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. For n : ℕ, connesHomologyAtHeight n is
(connesComplexAtHeight k A).homology n, the homology object in ModuleCat.{h} k.
