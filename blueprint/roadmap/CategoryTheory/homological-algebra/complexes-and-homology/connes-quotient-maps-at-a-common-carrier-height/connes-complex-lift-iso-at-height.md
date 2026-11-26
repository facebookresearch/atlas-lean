# Lifting the Connes quotient agrees with taking the lifted cokernel

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. Cokernel preservation gives U_h(connesComplex k
A) ≅ connesComplexAtHeight k A. The comparison is PreservesCokernel.iso applied to the first
horizontal map of the base cyclic bicomplex.
