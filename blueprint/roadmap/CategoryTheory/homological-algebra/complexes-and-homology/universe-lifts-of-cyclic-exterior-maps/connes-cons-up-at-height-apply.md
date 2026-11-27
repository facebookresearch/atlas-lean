# The first-column carrier lift sends an element to its up-lift

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ and x : A ⊗[k] TensorPower k n A,
connesConsUpAtHeight k A n x = ULift.up x in the first-column bicomplex term at height h.
