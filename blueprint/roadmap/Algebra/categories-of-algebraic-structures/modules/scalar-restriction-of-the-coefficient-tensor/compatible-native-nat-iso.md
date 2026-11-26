# Restricted coefficient-first tensor as an ordinary tensor functor

Let `R : Type u`, `S : Type w` be commutative rings with `Algebra R S`, and `M : ModuleCat.{t}
S`. The `S`-linear coefficient-first tensor functor `functorAt R S M : ModuleCat.{v} R →
ModuleCat.{max t v} S`, followed by restriction along `algebraMap R S`, is naturally
isomorphic to `L ↦ (Res_R M) ⊗_R L` in `ModuleCat R`. Its components preserve the tensor
entries `m,l`.
