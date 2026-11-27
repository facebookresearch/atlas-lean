# The base Connes term lifts to the raised-universe complex

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, connesTermUpAtHeight is the k-linear
carrier lift Cλ(A)_n → ULift(Cλ(A)_n), the degree-n term of the complex obtained by applying
ModuleCat.uliftFunctor from max u v to h. Its value is the inverse of the module up/down
equivalence.
