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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedCoefficientActions
public import Mathlib.Analysis.CStarAlgebra.Multiplier

/-!
# The actual coefficient multiplier homomorphism

The completed original left and right actions form a double centralizer.
Their source algebra, scalar and adjoint laws give the genuine nonunital
star-algebra homomorphism into the ordinary multiplier algebra of the same
seminorm completion. No multiplier carrier, coefficient map or norm estimate
is supplied as input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped MultiplierAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- The multiplier is the literal pair of completed original coefficient actions. -/
def coefficientMultiplier (a : A) : 𝓜(ℂ, p.NonUnitalCompletion) where
  fst := coefficientLeftCompletion μ α p a
  snd := coefficientRightCompletion μ α p a
  central := coefficientCompletion_central μ α p a

/-- The left multiplier component agrees with every original coefficient-core value. -/
theorem coefficientMultiplier_fst_apply (a : A) (f : Carrier μ α) :
    (coefficientMultiplier μ α p a).fst (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientLeft μ α a f) :=
  coefficientLeftCompletion_apply μ α p a f

/-- The right multiplier component agrees with every original coefficient-core value. -/
theorem coefficientMultiplier_snd_apply (a : A) (f : Carrier μ α) :
    (coefficientMultiplier μ α p a).snd (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientRight μ α a f) :=
  coefficientRightCompletion_apply μ α p a f

/-- The original coefficient algebra acts by its computed actual multiplier homomorphism. -/
def coefficientMultiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, p.NonUnitalCompletion) where
  toFun := coefficientMultiplier μ α p
  map_zero' := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_zero μ α p
    · exact coefficientRightCompletion_zero μ α p
  map_add' a b := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_add μ α p a b
    · exact coefficientRightCompletion_add μ α p a b
  map_smul' c a := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_smul μ α p c a
    · exact coefficientRightCompletion_smul μ α p c a
  map_mul' a b := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_mul μ α p a b
    · exact coefficientRightCompletion_mul μ α p a b
  map_star' a := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
    · change coefficientLeftCompletion μ α p (star a) x =
        star (coefficientRightCompletion μ α p a (star x))
      simpa only [star_star] using (star_coefficientRightCompletion μ α p a (star x)).symm
    · change coefficientRightCompletion μ α p (star a) x =
        star (coefficientLeftCompletion μ α p a (star x))
      simpa only [star_star] using (star_coefficientLeftCompletion μ α p a (star x)).symm

/-- The constructed coefficient homomorphism is exactly the computed centralizer pair. -/
@[simp]
theorem coefficientMultiplierHom_apply (a : A) :
    coefficientMultiplierHom μ α p a = coefficientMultiplier μ α p a := rfl

/-- The genuine coefficient multiplier retains the original coefficient norm bound. -/
theorem norm_coefficientMultiplier_le (a : A) : ‖coefficientMultiplier μ α p a‖ ≤ ‖a‖ := by
  rw [← DoubleCentralizer.norm_fst]
  exact norm_coefficientLeftCompletion_le μ α p a

end

end HaarTwistedCore
