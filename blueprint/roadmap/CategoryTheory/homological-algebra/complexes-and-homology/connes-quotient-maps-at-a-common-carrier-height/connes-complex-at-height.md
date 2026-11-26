# The Connes complex at height h is a first-column cokernel

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. connesComplexAtHeight is the cokernel in chain
complexes of (cyclicBicomplexAtHeight k A).d 1 0. It is the first-column Connes quotient in
ModuleCat.{h} k.
