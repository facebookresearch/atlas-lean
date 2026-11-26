# A whole tensor projects to the Connes term at the chosen height

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, connesTensorRepresentativeAtHeight :
TensorPower k (n + 1) A →ₗ[k] Cλ_h(A)_n first applies (TensorPower.consEquiv k A n).symm, then
connesConsUpAtHeight, then connesProjectionAtHeight.
