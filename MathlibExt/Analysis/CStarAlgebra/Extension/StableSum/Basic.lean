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
# Supplied matrix sums of Busby homomorphisms

The data consist of genuine compatible multiplier/corona matrix equivalences
and a Busby sum fixed by its literal diagonal formula. The source algebra
needs only the algebraic operations of BusbyHom; it need not be a complete,
normed or unital C-star algebra. The coefficient remains a genuine C-star
algebra for the existing multiplier and quotient APIs.

No standard stabilization, associativity, strong zero identity, quotient
class or inverse is manufactured by this carrier. Coherence and stable
relations are literal predicates, separate from their proof calculus.
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

/-- The literal two-by-two outer-multiplier diagonal, on the existing matrix carrier. -/
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

/-- Actual supplied matrix identifications and a sum constrained by its diagonal action. -/
structure StableSumData (A : Type uA) (B : Type uB)
    [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
    [NonUnitalCStarAlgebra B] where
  /-- The supplied equivalence from two-by-two multiplier matrices. -/
  multiplierMatrixEquiv :
    CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B) ≃⋆ₐ[ℂ] 𝓜(ℂ, B)
  /-- The compatible equivalence on outer-multiplier matrices. -/
  matrixEquiv :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    CStarMatrix (Fin 2) (Fin 2) (OuterMultiplier B) ≃⋆ₐ[ℂ] OuterMultiplier B
  quotient_compatible :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    ∀ M : CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B),
      matrixEquiv (M.map outerQuotientMap) =
        outerQuotientMap (multiplierMatrixEquiv M)
  /-- The Busby-homomorphism sum with the stated diagonal evaluation rule. -/
  sum : BusbyHom A B → BusbyHom A B → BusbyHom A B
  sum_apply :
    let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
    ∀ (tau₁ tau₂ : BusbyHom A B) (a : A),
      sum tau₁ tau₂ a = matrixEquiv (twoDiagonal (tau₁ a) (tau₂ a))

/-- Sum relative to the actual supplied matrix identifications. -/
abbrev busbySum (S : StableSumData A B) := S.sum

/-- The original associativity/strong-commutativity conjunction; no strong zero law. -/
def StableSumData.IsCoherent (S : StableSumData A B) : Prop :=
  (∀ tau₁ tau₂ tau₃ : BusbyHom A B,
    StronglyUnitaryEquivalent (S.sum (S.sum tau₁ tau₂) tau₃)
      (S.sum tau₁ (S.sum tau₂ tau₃))) ∧
  (∀ tau₁ tau₂ : BusbyHom A B,
    StronglyUnitaryEquivalent (S.sum tau₁ tau₂) (S.sum tau₂ tau₁))

/-- Stable strong equivalence compares sums with two actual trivial homomorphisms. -/
def StablyStrongEquivalent (S : StableSumData A B)
    (tau₁ tau₂ : BusbyHom A B) : Prop :=
  ∃ sigma₁ sigma₂,
    IsTrivial sigma₁ ∧ IsTrivial sigma₂ ∧
      StronglyUnitaryEquivalent (S.sum tau₁ sigma₁) (S.sum tau₂ sigma₂)

/-- The literal stable weak relation, with the same actual trivial summands. -/
def StablyWeakEquivalent (S : StableSumData A B)
    (tau₁ tau₂ : BusbyHom A B) : Prop :=
  ∃ sigma₁ sigma₂,
    IsTrivial sigma₁ ∧ IsTrivial sigma₂ ∧
      WeaklyUnitaryEquivalent (S.sum tau₁ sigma₁) (S.sum tau₂ sigma₂)

end CStarExtension
