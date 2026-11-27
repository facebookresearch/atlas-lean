# The cyclic bicomplex lifts in both complex directions

Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. cyclicBicomplexAtHeight applies U_h in each cell
of cyclicBicomplex k A, using down ℕ in both directions. Its horizontal and vertical maps are
the images of the base bicomplex maps.
