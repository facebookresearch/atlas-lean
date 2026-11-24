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

public import MathlibExt.MeasureTheory.VectorMeasure.RegularVariation
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Regular signed measures and integration on continuous functions

This file packages the real signed measures whose total variation is regular as
a real submodule.  On a compact Borel space, integration against such a measure
is a bounded real functional on the continuous real-valued functions.  The
construction installs no regularity or norm instance on the ambient type of
signed measures.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace MathlibExt.MeasureTheory

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [R1Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Signed measures with regular total variation, as a real submodule of all
signed measures. -/
noncomputable def regularSignedMeasureSubmodule (X : Type u)
    [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X] :
    Submodule ℝ (SignedMeasure X) where
  carrier := {s | s.totalVariation.Regular}
  zero_mem' :=
    (SignedMeasure.totalVariation_regular_iff_hasRegularVariation
      (0 : SignedMeasure X)).2 VectorMeasure.HasRegularVariation.zero
  add_mem' := by
    intro s t hs ht
    apply (SignedMeasure.totalVariation_regular_iff_hasRegularVariation (s + t)).2
    let _ : IsFiniteMeasure s.variation := by
      rw [← SignedMeasure.totalVariation_eq_variation]
      infer_instance
    let _ : IsFiniteMeasure t.variation := by
      rw [← SignedMeasure.totalVariation_eq_variation]
      infer_instance
    exact ((SignedMeasure.totalVariation_regular_iff_hasRegularVariation s).1 hs).add
      ((SignedMeasure.totalVariation_regular_iff_hasRegularVariation t).1 ht)
  smul_mem' := by
    intro c s hs
    exact (SignedMeasure.totalVariation_regular_iff_hasRegularVariation (c • s)).2
      (((SignedMeasure.totalVariation_regular_iff_hasRegularVariation s).1 hs).smul c)

/-- A real signed measure whose total variation is regular. -/
abbrev RegularSignedMeasure (X : Type u) [TopologicalSpace X] [R1Space X]
    [MeasurableSpace X] [BorelSpace X] :=
  ↑(regularSignedMeasureSubmodule X)

namespace RegularSignedMeasure

/-- The defining regularity property of a regular signed measure. -/
theorem totalVariation_regular (s : RegularSignedMeasure X) :
    (s : SignedMeasure X).totalVariation.Regular :=
  s.property

/-- A regular signed measure has regular variation in the generic vector-measure sense. -/
theorem hasRegularVariation (s : RegularSignedMeasure X) :
    VectorMeasure.HasRegularVariation (s : SignedMeasure X) :=
  (SignedMeasure.totalVariation_regular_iff_hasRegularVariation (s : SignedMeasure X)).1
    s.property

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] in
private theorem variationFinite (s : SignedMeasure X) :
    IsFiniteMeasure s.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

variable [CompactSpace X]

omit [R1Space X] in
private theorem continuousMap_integrable (s : SignedMeasure X) (f : C(X, ℝ)) :
    s.Integrable fun x ↦ f x := by
  let _ : IsFiniteMeasure s.variation := variationFinite s
  apply Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm x

private noncomputable def signedIntegralLinear (s : RegularSignedMeasure X) :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ᵛ x, f x ∂<•(s : SignedMeasure X)
  map_add' f g := by
    simpa only [ContinuousMap.add_apply] using
      (VectorMeasure.integral_fun_add
        (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
        (continuousMap_integrable (s : SignedMeasure X) f)
        (continuousMap_integrable (s : SignedMeasure X) g))
  map_smul' c f := by
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply] using
      (VectorMeasure.integral_fun_smul (s : SignedMeasure X)
        (ContinuousLinearMap.lsmul ℝ ℝ).flip c (fun x ↦ f x))

@[simp]
private theorem signedIntegralLinear_apply (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    signedIntegralLinear s f = ∫ᵛ x, f x ∂<•(s : SignedMeasure X) :=
  rfl

private theorem norm_signedIntegralLinear_apply_le
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    ‖signedIntegralLinear s f‖ ≤
      (s : SignedMeasure X).totalVariation.real univ * ‖f‖ := by
  let _ : IsFiniteMeasure (s : SignedMeasure X).variation :=
    variationFinite (s : SignedMeasure X)
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := (s : SignedMeasure X))
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (f := fun x ↦ f x)
    (Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm x)
  simpa [signedIntegralLinear, SignedMeasure.totalVariation_eq_variation,
    mul_comm] using h

/-- Integration against a regular signed measure, as a bounded functional on
the continuous real-valued functions. -/
@[no_expose]
noncomputable def signedIntegralDual (s : RegularSignedMeasure X) :
    StrongDual ℝ C(X, ℝ) :=
  LinearMap.mkContinuous (signedIntegralLinear s)
    ((s : SignedMeasure X).totalVariation.real univ)
    (norm_signedIntegralLinear_apply_le s)

/-- The continuous signed-integral functional evaluates by vector-measure integration. -/
@[simp]
theorem signedIntegralDual_apply (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    signedIntegralDual s f = ∫ᵛ x, f x ∂<•(s : SignedMeasure X) :=
  by
    simp only [signedIntegralDual, LinearMap.mkContinuous_apply,
      signedIntegralLinear_apply]

/-- The pointwise total-variation bound for signed integration. -/
theorem norm_signedIntegralDual_apply_le
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    ‖signedIntegralDual s f‖ ≤
      (s : SignedMeasure X).totalVariation.real univ * ‖f‖ :=
  by
    simpa only [signedIntegralDual, LinearMap.mkContinuous_apply] using
      norm_signedIntegralLinear_apply_le s f

/-- The operator norm of signed integration is bounded by the total mass of
the total variation. -/
theorem norm_signedIntegralDual_le (s : RegularSignedMeasure X) :
    ‖signedIntegralDual s‖ ≤ (s : SignedMeasure X).totalVariation.real univ := by
  apply ContinuousLinearMap.opNorm_le_bound _ measureReal_nonneg
  exact norm_signedIntegralDual_apply_le s

/-- Integration is real-linear in a regular signed measure. -/
@[no_expose]
noncomputable def regularSignedMeasureIntegral :
    RegularSignedMeasure X →ₗ[ℝ] StrongDual ℝ C(X, ℝ) where
  toFun := signedIntegralDual
  map_add' s t := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [signedIntegralDual_apply, add_apply]
    change (∫ᵛ x, f x ∂<•((s : SignedMeasure X) + (t : SignedMeasure X))) =
      (∫ᵛ x, f x ∂<•(s : SignedMeasure X)) +
        ∫ᵛ x, f x ∂<•(t : SignedMeasure X)
    exact VectorMeasure.integral_add_vectorMeasure
      (continuousMap_integrable (s : SignedMeasure X) f)
      (continuousMap_integrable (t : SignedMeasure X) f)
  map_smul' c s := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [signedIntegralDual_apply, smul_apply, RingHom.id_apply]
    change (∫ᵛ x, f x ∂<•(c • (s : SignedMeasure X))) =
      c • ∫ᵛ x, f x ∂<•(s : SignedMeasure X)
    exact VectorMeasure.integral_smul_vectorMeasure (fun x ↦ f x) c

/-- The zero regular signed measure has the zero integral functional. -/
@[simp]
theorem signedIntegralDual_zero :
    signedIntegralDual (0 : RegularSignedMeasure X) = 0 :=
  (regularSignedMeasureIntegral (X := X)).map_zero

/-- The signed integral functional is additive in the regular signed measure. -/
@[simp]
theorem signedIntegralDual_add (s t : RegularSignedMeasure X) :
    signedIntegralDual (s + t) = signedIntegralDual s + signedIntegralDual t :=
  (regularSignedMeasureIntegral (X := X)).map_add s t

/-- The signed integral functional commutes with real scalar multiplication of the measure. -/
@[simp]
theorem signedIntegralDual_smul (c : ℝ) (s : RegularSignedMeasure X) :
    signedIntegralDual (c • s) = c • signedIntegralDual s :=
  (regularSignedMeasureIntegral (X := X)).map_smul c s

/-- Negating a regular signed measure negates its integral functional. -/
@[simp]
theorem signedIntegralDual_neg (s : RegularSignedMeasure X) :
    signedIntegralDual (-s) = -signedIntegralDual s :=
  (regularSignedMeasureIntegral (X := X)).map_neg s

/-- The signed integral functional takes a difference of measures to the difference of their functionals. -/
@[simp]
theorem signedIntegralDual_sub (s t : RegularSignedMeasure X) :
    signedIntegralDual (s - t) = signedIntegralDual s - signedIntegralDual t :=
  (regularSignedMeasureIntegral (X := X)).map_sub s t

/-- The linear integration map evaluates by integration against the underlying signed measure. -/
@[simp]
theorem regularSignedMeasureIntegral_apply
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    regularSignedMeasureIntegral s f =
      ∫ᵛ x, f x ∂<•(s : SignedMeasure X) :=
  signedIntegralDual_apply s f

end RegularSignedMeasure

end

end MathlibExt.MeasureTheory
