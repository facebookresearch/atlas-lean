# The first-factor tensor object lifts to the first bicomplex column

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, connesConsUpAtHeight is the k-linear map A
⊗[k] TensorPower k n A → (cyclicBicomplexAtHeight k A).X 0.X n with value x ↦ ULift.up x.
