# The higher representative is the base representative followed by lift comparison

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Write U_n : Cλ(A)_n → ULift(Cλ(A)_n) for
connesTermUpAtHeight and J_n : ULift(Cλ(A)_n) ≃ Cλ_h(A)_n for the component of the canonical
Connes lift comparison. For x : TensorPower k (n + 1) A, q_h(x) = J_n.hom(U_n(q_base(x))),
where q_base is connesTensorRepresentative in the base universe.
