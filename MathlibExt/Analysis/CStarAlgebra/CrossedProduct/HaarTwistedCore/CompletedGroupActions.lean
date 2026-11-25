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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormGroupActions
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Original group translations on the same-seminorm completion

The literal inverse left translation and modular right translation preserve
every actual C-star seminorm. Extend their original linear maps along the
actual dense separated-completion map. The completed maps have their exact
original core values and form the same compatible centralizer pair.
The zero seminorm is allowed; no group multiplier or invariance is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

/-- The actual inverse left group translation on the same-seminorm completion. -/
def groupLeftCompletion (g : G) : p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (groupLeft μ α g)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- The actual modular right group translation on the same-seminorm completion. -/
def groupRightCompletion (g : G) : p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (groupRight μ α g)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- Completed inverse left translation retains every original Haar-core value. -/
theorem groupLeftCompletion_apply (g : G) (f : Carrier μ α) :
    groupLeftCompletion μ α p g (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupLeft μ α g f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨1, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (groupLeft μ α g h)‖ ≤
    1 * ‖p.toNonUnitalCompletion h‖
  simp only [CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupLeft, one_mul, le_rfl]

/-- Completed modular right translation retains every original Haar-core value. -/
theorem groupRightCompletion_apply (g : G) (f : Carrier μ α) :
    groupRightCompletion μ α p g (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupRight μ α g f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨1, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (groupRight μ α g h)‖ ≤
    1 * ‖p.toNonUnitalCompletion h‖
  simp only [CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupRight, one_mul, le_rfl]

/-- The completed inverse left translation preserves the actual same-seminorm norm. -/
theorem norm_groupLeftCompletion_apply (g : G) (x : p.NonUnitalCompletion) :
    ‖groupLeftCompletion μ α p g x‖ = ‖x‖ := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p g).continuous.norm continuous_norm ?_) x
  funext f
  simp only [Function.comp_apply, groupLeftCompletion_apply,
    CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupLeft]

/-- The completed modular right translation preserves the actual same-seminorm norm. -/
theorem norm_groupRightCompletion_apply (g : G) (x : p.NonUnitalCompletion) :
    ‖groupRightCompletion μ α p g x‖ = ‖x‖ := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p g).continuous.norm continuous_norm ?_) x
  funext f
  simp only [Function.comp_apply, groupRightCompletion_apply,
    CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupRight]

/-- The group identity acts by the actual completed left identity operator. -/
@[simp]
theorem groupLeftCompletion_one : groupLeftCompletion μ α p (1 : G) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p 1).continuous continuous_id ?_) x
  funext f
  simp only [Function.comp_apply, groupLeftCompletion_apply, groupLeft_one, LinearMap.id_apply, id_eq]

/-- The group identity acts by the actual completed right identity operator. -/
@[simp]
theorem groupRightCompletion_one : groupRightCompletion μ α p (1 : G) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p 1).continuous continuous_id ?_) x
  funext f
  simp only [Function.comp_apply, groupRightCompletion_apply, groupRight_one, LinearMap.id_apply, id_eq]

/-- Completed inverse left translations compose in the original group order. -/
theorem groupLeftCompletion_mul (g h : G) :
    groupLeftCompletion μ α p (g * h) =
      (groupLeftCompletion μ α p g).comp (groupLeftCompletion μ α p h) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p (g * h)).continuous
    ((groupLeftCompletion μ α p g).continuous.comp
      (groupLeftCompletion μ α p h).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    groupLeftCompletion_apply, groupLeft_mul, LinearMap.comp_apply]

/-- Completed modular right translations compose in the original centralizer order. -/
theorem groupRightCompletion_mul (g h : G) :
    groupRightCompletion μ α p (g * h) =
      (groupRightCompletion μ α p h).comp (groupRightCompletion μ α p g) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p (g * h)).continuous
    ((groupRightCompletion μ α p h).continuous.comp
      (groupRightCompletion μ α p g).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    groupRightCompletion_apply, groupRight_mul, LinearMap.comp_apply]

/-- The completed star exchanges inverse left translation with inverse right translation. -/
theorem star_groupLeftCompletion (g : G) (x : p.NonUnitalCompletion) :
    star (groupLeftCompletion μ α p g x) = groupRightCompletion μ α p g⁻¹ (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p g).continuous.star
    ((groupRightCompletion μ α p g⁻¹).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    groupLeftCompletion_apply, ← map_star, groupRightCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_groupLeft μ α g f)

/-- The completed star exchanges modular right translation with inverse left translation. -/
theorem star_groupRightCompletion (g : G) (x : p.NonUnitalCompletion) :
    star (groupRightCompletion μ α p g x) = groupLeftCompletion μ α p g⁻¹ (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p g).continuous.star
    ((groupLeftCompletion μ α p g⁻¹).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    groupRightCompletion_apply, ← map_star, groupLeftCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_groupRight μ α g f)

/-- The computed completed translations form the actual original group centralizer pair. -/
theorem groupCompletion_central (g : G) (x y : p.NonUnitalCompletion) :
    groupRightCompletion μ α p g x * y = x * groupLeftCompletion μ α p g y := by
  refine (p.denseRange_toNonUnitalCompletion).induction_on₂
    (p := fun u v : p.NonUnitalCompletion =>
      groupRightCompletion μ α p g u * v = u * groupLeftCompletion μ α p g v)
    ?_ ?_ x y
  · exact isClosed_eq
      (((groupRightCompletion μ α p g).continuous.comp continuous_fst).mul continuous_snd)
      (continuous_fst.mul ((groupLeftCompletion μ α p g).continuous.comp continuous_snd))
  · intro f h
    rw [groupRightCompletion_apply, groupLeftCompletion_apply, ← map_mul, ← map_mul]
    exact congrArg p.toNonUnitalCompletion (convolution_groupLeft μ α g f h).symm

end

end HaarTwistedCore
