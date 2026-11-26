# The normalized higher exterior map divides by the input count

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Assume k is a ℚ-algebra. For n : ℕ,
cyclicExteriorAtHeight is algebraMap ℚ k ((n + 1 : ℚ)⁻¹) times cyclicFullExteriorAtHeight :
⋀[k]^(n+1) A →ₗ[k] Cλ_h(A)_n.
