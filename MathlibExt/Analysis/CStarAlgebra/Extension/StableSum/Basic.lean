/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Extension.BusbyRelations
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Compatible matrix sums of Busby homomorphisms

Let `B` be a nonunital C-star algebra, `q : M(B) → Q(B)` its quotient, and `A` a possibly
nonunital, nonassociative semiring with distributive complex scalar action and additive
involution. A stable-sum datum consists of star-algebra equivalences `F_M : M₂(M(B)) ≃ M(B)` and
`F_Q : M₂(Q(B)) ≃ Q(B)` with `q ∘ F_M = F_Q ∘ q₂`. The sum is constrained by `S.sum τ₁ τ₂ a =
F_Q(diag(τ₁(a),τ₂(a)))`.

Coherence means associativity and commutativity up to strong multiplier-unitary equivalence.
Stable strong or weak equivalence means that adjoining liftable Busby maps on the two sides
gives, respectively, multiplier-unitary or corona-unitary conjugate sums. All these notions are
relative to the specified fold datum `S`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra Matrix MultiplierAlgebra

namespace CStarExtension

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
variable [NonUnitalCStarAlgebra B]

/-- **Two-by-two corona diagonal.** For `x,y : Q(B)`, `twoDiagonal x y` is the matrix `diag(x,y)`,
with these diagonal entries and zero off-diagonal entries. -/
def twoDiagonal (x y : OuterMultiplier B) :
    CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B) :=
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  fun i j => if i = j then if i = 0 then x else y else 0

@[simp]
theorem twoDiagonal_zero_zero (x y : OuterMultiplier B) :
    twoDiagonal x y 0 0 = x :=
  rfl

@[simp]
theorem twoDiagonal_one_one (x y : OuterMultiplier B) :
    twoDiagonal x y 1 1 = y :=
  rfl

@[simp]
theorem twoDiagonal_zero_one (x y : OuterMultiplier B) :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    twoDiagonal x y 0 1 = 0 := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  rfl

@[simp]
theorem twoDiagonal_one_zero (x y : OuterMultiplier B) :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    twoDiagonal x y 1 0 = 0 := by
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  rfl

/-- **Compatible multiplier and corona matrix folds.** This record contains star-algebra
equivalences `F_M : M₂(M(B)) ≃ M(B)` and `F_Q : M₂(Q(B)) ≃ Q(B)` satisfying `q ∘ F_M = F_Q ∘
q₂`, and a Busby sum with `S.sum τ₁ τ₂ a = F_Q(diag(τ₁(a),τ₂(a)))`. The domain `A` requires
only the displayed semiring, scalar-action and additive-involution structure. -/
structure StableSumData (A : Type uA) (B : Type uB)
    [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
    [NonUnitalCStarAlgebra B] where
  /-- **Multiplier matrix fold.** A star-algebra equivalence from the two-by-two multiplier
  matrices `M₂(M(B))` to `M(B)`. -/
  multiplierMatrixEquiv :
    CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B) ≃⋆ₐ[ℂ] 𝓜(ℂ, B)
  /-- **Corona matrix fold.** A star-algebra equivalence `M₂(Q(B)) ≃ Q(B)` compatible with the
  multiplier fold through the quotient map. -/
  matrixEquiv :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B) ≃⋆ₐ[ℂ] OuterMultiplier B
  quotient_compatible :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    ∀ M : CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B),
      matrixEquiv (M.map outerQuotientMap) =
        outerQuotientMap (multiplierMatrixEquiv M)
  /-- **Diagonal Busby sum.** The sum of two homomorphisms is required to satisfy `sum τ₁ τ₂ a =
  matrixEquiv (diag(τ₁(a),τ₂(a)))` for every `a : A`. -/
  sum : BusbyHom A B → BusbyHom A B → BusbyHom A B
  sum_apply :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    ∀ (tau₁ tau₂ : BusbyHom A B) (a : A),
      sum tau₁ tau₂ a = matrixEquiv (twoDiagonal (tau₁ a) (tau₂ a))

/-- **Busby sum relative to a matrix fold.** `busbySum S = S.sum`, the operation induced pointwise
by the corona fold applied to the two-by-two diagonal. -/
abbrev busbySum (S : StableSumData A B) := S.sum

/-- **Associativity and commutativity of a Busby sum.** Coherence of `S` means strong unitary
equivalence of the two parenthesizations of each triple sum and of the two orders of each pair
sum. -/
def StableSumData.IsCoherent (S : StableSumData A B) : Prop :=
  (∀ tau₁ tau₂ tau₃ : BusbyHom A B,
    StronglyUnitaryEquivalent (S.sum (S.sum tau₁ tau₂) tau₃)
      (S.sum tau₁ (S.sum tau₂ tau₃))) ∧
  (∀ tau₁ tau₂ : BusbyHom A B,
    StronglyUnitaryEquivalent (S.sum tau₁ tau₂) (S.sum tau₂ tau₁))

/-- **Stable strong equivalence relative to a fold.** Two Busby maps are stably strongly
equivalent when there are liftable `σ₁,σ₂` such that `S.sum τ₁ σ₁` and `S.sum τ₂ σ₂` differ by
conjugation by the image of one unitary of `M(B)`. -/
def StablyStrongEquivalent (S : StableSumData A B)
    (tau₁ tau₂ : BusbyHom A B) : Prop :=
  ∃ sigma₁ sigma₂,
    IsTrivial sigma₁ ∧ IsTrivial sigma₂ ∧
      StronglyUnitaryEquivalent (S.sum tau₁ sigma₁) (S.sum tau₂ sigma₂)

/-- **Stable weak equivalence relative to a fold.** Two Busby maps are stably weakly equivalent
when adjoining liftable `σ₁,σ₂` makes their `S`-sums conjugate by one unitary of `Q(B)`. -/
def StablyWeakEquivalent (S : StableSumData A B)
    (tau₁ tau₂ : BusbyHom A B) : Prop :=
  ∃ sigma₁ sigma₂,
    IsTrivial sigma₁ ∧ IsTrivial sigma₂ ∧
      WeaklyUnitaryEquivalent (S.sum tau₁ sigma₁) (S.sum tau₂ sigma₂)

end CStarExtension
