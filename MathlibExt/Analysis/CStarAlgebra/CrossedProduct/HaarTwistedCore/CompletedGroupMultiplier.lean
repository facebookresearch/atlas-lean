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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedGroupActions
public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Algebra.Star.Unitary

/-!
# Actual group unitaries in the same-seminorm multiplier algebra

The original completed left and modular right translations form the actual
group multiplier. Their inverse and adjoint formulas prove its unitarity,
giving the computed homomorphism into the ordinary unitary multiplier group.
The source's full-norm comparison, group embedding and strict continuity
remain separate obligations. The zero completion is allowed.
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
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- The group multiplier is the actual completed original translation pair. -/
def groupMultiplier (g : G) : 𝓜(ℂ, p.NonUnitalCompletion) where
  fst := groupLeftCompletion μ α p g
  snd := groupRightCompletion μ α p g
  central := groupCompletion_central μ α p g

/-- The left group multiplier component has the original inverse-translation core values. -/
theorem groupMultiplier_fst_apply (g : G) (f : Carrier μ α) :
    (groupMultiplier μ α p g).fst (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupLeft μ α g f) :=
  groupLeftCompletion_apply μ α p g f

/-- The right group multiplier component has the original modular-translation core values. -/
theorem groupMultiplier_snd_apply (g : G) (f : Carrier μ α) :
    (groupMultiplier μ α p g).snd (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupRight μ α g f) :=
  groupRightCompletion_apply μ α p g f

/-- The original group acts by its actual computed multiplier homomorphism. -/
def groupMultiplierHom : G →* 𝓜(ℂ, p.NonUnitalCompletion) where
  toFun := groupMultiplier μ α p
  map_one' := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact groupLeftCompletion_one μ α p
    · exact groupRightCompletion_one μ α p
  map_mul' g h := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact groupLeftCompletion_mul μ α p g h
    · exact groupRightCompletion_mul μ α p g h

/-- The group homomorphism retains the literal computed multiplier pair. -/
@[simp]
theorem groupMultiplierHom_apply (g : G) :
    groupMultiplierHom μ α p g = groupMultiplier μ α p g := rfl

/-- The actual group multiplier adjoint is the multiplier of the original inverse group element. -/
theorem star_groupMultiplier (g : G) :
    star (groupMultiplier μ α p g) = groupMultiplier μ α p g⁻¹ := by
  apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
  · change star (groupRightCompletion μ α p g (star x)) = groupLeftCompletion μ α p g⁻¹ x
    simpa only [star_star] using star_groupRightCompletion μ α p g (star x)
  · change star (groupLeftCompletion μ α p g (star x)) = groupRightCompletion μ α p g⁻¹ x
    simpa only [star_star] using star_groupLeftCompletion μ α p g (star x)

/-- The computed original group multiplier is an actual unitary, including in the zero completion. -/
theorem groupMultiplier_mem_unitary (g : G) :
    groupMultiplier μ α p g ∈ unitary 𝓜(ℂ, p.NonUnitalCompletion) := by
  change star (groupMultiplier μ α p g) * groupMultiplier μ α p g = 1 ∧
    groupMultiplier μ α p g * star (groupMultiplier μ α p g) = 1
  simp only [star_groupMultiplier]
  constructor
  · change groupMultiplierHom μ α p g⁻¹ * groupMultiplierHom μ α p g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  · change groupMultiplierHom μ α p g * groupMultiplierHom μ α p g⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]

/-- The actual group homomorphism into the ordinary unitary group of the same-seminorm multipliers. -/
def groupUnitaryMultiplierHom : G →* unitary 𝓜(ℂ, p.NonUnitalCompletion) where
  toFun g := ⟨groupMultiplierHom μ α p g, groupMultiplier_mem_unitary μ α p g⟩
  map_one' := Subtype.ext (map_one (groupMultiplierHom μ α p))
  map_mul' g h := Subtype.ext (map_mul (groupMultiplierHom μ α p) g h)

/-- The unitary-valued group map retains exactly the computed multiplier. -/
@[simp]
theorem groupUnitaryMultiplierHom_coe (g : G) :
    ((groupUnitaryMultiplierHom μ α p g : unitary 𝓜(ℂ, p.NonUnitalCompletion)) :
      𝓜(ℂ, p.NonUnitalCompletion)) = groupMultiplier μ α p g := rfl

/-- The actual group multiplier has operator norm at most one; zero completions remain legal. -/
theorem norm_groupMultiplier_le_one (g : G) : ‖groupMultiplier μ α p g‖ ≤ 1 := by
  rw [← DoubleCentralizer.norm_fst]
  apply (groupLeftCompletion μ α p g).opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using (norm_groupLeftCompletion_apply μ α p g x).le

end

end HaarTwistedCore
