# A higher pure exterior word has the full signed permutation formula

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For a : Fin (n + 1) → A, cyclicFullExteriorAtHeight n
(ιMulti a) = ∑ σ : Perm(Fin(n+1)), sign(σ) • q_h(tprod(a ∘ σ)). The tuple is reindexed by σ
itself.
