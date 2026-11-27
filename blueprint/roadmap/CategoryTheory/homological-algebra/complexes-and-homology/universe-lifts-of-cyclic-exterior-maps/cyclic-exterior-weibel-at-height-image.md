# The degree-signed higher map equals lift of the degree-signed base map

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Write U_n : Cλ(A)_n → ULift(Cλ(A)_n) for
connesTermUpAtHeight and J_n : ULift(Cλ(A)_n) ≃ Cλ_h(A)_n for the component of the canonical
Connes lift comparison. If k is a ℚ-algebra, cyclicExteriorWeibelAtHeight n = J_n.hom ∘ U_n ∘
cyclicExteriorWeibel n. Both maps retain the degree factor (−1)^n.
