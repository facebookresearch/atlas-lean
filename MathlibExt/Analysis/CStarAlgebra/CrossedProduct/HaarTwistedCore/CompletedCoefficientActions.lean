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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormCoefficientActions
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Actual coefficient actions on the same-seminorm completion

Each original coefficient map is extended along the actual dense separated
completion map. The bounds are proved from the coefficient square identity,
and the extension agrees with the literal original compact-support values.
The zero seminorm and the zero coefficient algebra are included.
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
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- The actual left coefficient map on the completion of the same original seminorm. -/
def coefficientLeftCompletion (a : A) :
    p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (coefficientLeft μ α a)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- The actual right coefficient map on the completion of the same original seminorm. -/
def coefficientRightCompletion (a : A) :
    p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (coefficientRight μ α a)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- Completed left multiplication has exactly the original coefficient values on the dense core. -/
theorem coefficientLeftCompletion_apply (a : A) (f : Carrier μ α) :
    coefficientLeftCompletion μ α p a (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientLeft μ α a f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨‖a‖, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (coefficientLeft μ α a h)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion h‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientLeft_le μ α p a h

/-- Completed right multiplication has exactly the original coefficient values on the dense core. -/
theorem coefficientRightCompletion_apply (a : A) (f : Carrier μ α) :
    coefficientRightCompletion μ α p a (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientRight μ α a f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨‖a‖, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (coefficientRight μ α a h)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion h‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientRight_le μ α p a h

/-- The completed left action retains the actual original coefficient norm bound. -/
theorem norm_coefficientLeftCompletion_apply_le (a : A) (x : p.NonUnitalCompletion) :
    ‖coefficientLeftCompletion μ α p a x‖ ≤ ‖a‖ * ‖x‖ := by
  apply LinearMap.norm_extendOfNorm_apply_le (p.denseRange_toNonUnitalCompletion) ‖a‖
  intro f
  change ‖p.toNonUnitalCompletion (coefficientLeft μ α a f)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion f‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientLeft_le μ α p a f

/-- The completed right action retains the actual original coefficient norm bound. -/
theorem norm_coefficientRightCompletion_apply_le (a : A) (x : p.NonUnitalCompletion) :
    ‖coefficientRightCompletion μ α p a x‖ ≤ ‖a‖ * ‖x‖ := by
  apply LinearMap.norm_extendOfNorm_apply_le (p.denseRange_toNonUnitalCompletion) ‖a‖
  intro f
  change ‖p.toNonUnitalCompletion (coefficientRight μ α a f)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion f‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientRight_le μ α p a f

/-- The computed completed left operator has norm at most the original coefficient norm. -/
theorem norm_coefficientLeftCompletion_le (a : A) :
    ‖coefficientLeftCompletion μ α p a‖ ≤ ‖a‖ :=
  (coefficientLeftCompletion μ α p a).opNorm_le_bound (norm_nonneg a)
    (norm_coefficientLeftCompletion_apply_le μ α p a)

/-- The computed completed right operator has norm at most the original coefficient norm. -/
theorem norm_coefficientRightCompletion_le (a : A) :
    ‖coefficientRightCompletion μ α p a‖ ≤ ‖a‖ :=
  (coefficientRightCompletion μ α p a).opNorm_le_bound (norm_nonneg a)
    (norm_coefficientRightCompletion_apply_le μ α p a)

/-- Zero acts by the zero completed left operator. -/
@[simp]
theorem coefficientLeftCompletion_zero : coefficientLeftCompletion μ α p (0 : A) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p 0).continuous continuous_const ?_) x
  funext f
  simp only [Function.comp_apply, coefficientLeftCompletion_apply, zero_apply]
  have h : coefficientLeft μ α (0 : A) f = 0 := by
    apply ext μ α
    intro s
    simp only [coefficientLeft_apply, zero_mul]
    rfl
  rw [h, map_zero]

/-- Zero acts by the zero completed right operator. -/
@[simp]
theorem coefficientRightCompletion_zero : coefficientRightCompletion μ α p (0 : A) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p 0).continuous continuous_const ?_) x
  funext f
  simp only [Function.comp_apply, coefficientRightCompletion_apply, zero_apply]
  have h : coefficientRight μ α (0 : A) f = 0 := by
    apply ext μ α
    intro s
    simp only [coefficientRight_apply, α.apply_zero, mul_zero]
    rfl
  rw [h, map_zero]

/-- Adding original coefficients adds their actual completed left operators. -/
theorem coefficientLeftCompletion_add (a b : A) :
    coefficientLeftCompletion μ α p (a + b) =
      coefficientLeftCompletion μ α p a + coefficientLeftCompletion μ α p b := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p (a + b)).continuous
    ((coefficientLeftCompletion μ α p a).continuous.add
      (coefficientLeftCompletion μ α p b).continuous) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.add_apply,
    coefficientLeftCompletion_apply, coefficientLeft_add, LinearMap.add_apply, map_add]

/-- Adding original coefficients adds their actual completed right operators. -/
theorem coefficientRightCompletion_add (a b : A) :
    coefficientRightCompletion μ α p (a + b) =
      coefficientRightCompletion μ α p a + coefficientRightCompletion μ α p b := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p (a + b)).continuous
    ((coefficientRightCompletion μ α p a).continuous.add
      (coefficientRightCompletion μ α p b).continuous) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.add_apply,
    coefficientRightCompletion_apply, coefficientRight_add, LinearMap.add_apply, map_add]

/-- Scaling an original coefficient scales its actual completed left operator. -/
theorem coefficientLeftCompletion_smul (c : ℂ) (a : A) :
    coefficientLeftCompletion μ α p (c • a) = c • coefficientLeftCompletion μ α p a := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p (c • a)).continuous
    ((coefficientLeftCompletion μ α p a).continuous.const_smul c) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.smul_apply,
    coefficientLeftCompletion_apply, coefficientLeft_smul, LinearMap.smul_apply, map_smul]

/-- Scaling an original coefficient scales its actual completed right operator. -/
theorem coefficientRightCompletion_smul (c : ℂ) (a : A) :
    coefficientRightCompletion μ α p (c • a) = c • coefficientRightCompletion μ α p a := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p (c • a)).continuous
    ((coefficientRightCompletion μ α p a).continuous.const_smul c) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.smul_apply,
    coefficientRightCompletion_apply, coefficientRight_smul, LinearMap.smul_apply, map_smul]

/-- Completed left coefficients compose in the original algebra order. -/
theorem coefficientLeftCompletion_mul (a b : A) :
    coefficientLeftCompletion μ α p (a * b) =
      (coefficientLeftCompletion μ α p a).comp (coefficientLeftCompletion μ α p b) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p (a * b)).continuous
    ((coefficientLeftCompletion μ α p a).continuous.comp
      (coefficientLeftCompletion μ α p b).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    coefficientLeftCompletion_apply, coefficientLeft_mul, LinearMap.comp_apply]

/-- Completed right coefficients compose in the original double-centralizer order. -/
theorem coefficientRightCompletion_mul (a b : A) :
    coefficientRightCompletion μ α p (a * b) =
      (coefficientRightCompletion μ α p b).comp (coefficientRightCompletion μ α p a) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p (a * b)).continuous
    ((coefficientRightCompletion μ α p b).continuous.comp
      (coefficientRightCompletion μ α p a).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    coefficientRightCompletion_apply, coefficientRight_mul, LinearMap.comp_apply]

/-- The completed involution exchanges left coefficients with adjoint right coefficients. -/
theorem star_coefficientLeftCompletion (a : A) (x : p.NonUnitalCompletion) :
    star (coefficientLeftCompletion μ α p a x) =
      coefficientRightCompletion μ α p (star a) (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p a).continuous.star
    ((coefficientRightCompletion μ α p (star a)).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    coefficientLeftCompletion_apply, ← map_star, coefficientRightCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_coefficientLeft μ α a f)

/-- The completed involution exchanges right coefficients with adjoint left coefficients. -/
theorem star_coefficientRightCompletion (a : A) (x : p.NonUnitalCompletion) :
    star (coefficientRightCompletion μ α p a x) =
      coefficientLeftCompletion μ α p (star a) (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p a).continuous.star
    ((coefficientLeftCompletion μ α p (star a)).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    coefficientRightCompletion_apply, ← map_star, coefficientLeftCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_coefficientRight μ α a f)

/-- The two computed completed coefficient maps are an actual compatible centralizer pair. -/
theorem coefficientCompletion_central (a : A) (x y : p.NonUnitalCompletion) :
    coefficientRightCompletion μ α p a x * y = x * coefficientLeftCompletion μ α p a y := by
  refine (p.denseRange_toNonUnitalCompletion).induction_on₂
    (p := fun u v : p.NonUnitalCompletion =>
      coefficientRightCompletion μ α p a u * v = u * coefficientLeftCompletion μ α p a v)
    ?_ ?_ x y
  · exact isClosed_eq
      (((coefficientRightCompletion μ α p a).continuous.comp continuous_fst).mul continuous_snd)
      (continuous_fst.mul ((coefficientLeftCompletion μ α p a).continuous.comp continuous_snd))
  · intro f h
    rw [coefficientRightCompletion_apply, coefficientLeftCompletion_apply, ← map_mul, ← map_mul]
    exact congrArg p.toNonUnitalCompletion (convolution_coefficientLeft μ α a f h).symm

end

end HaarTwistedCore
