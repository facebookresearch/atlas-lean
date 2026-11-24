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

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Positive Riesz--Markov representation on a compact space

On a compact Hausdorff Borel space, continuous functions and compactly supported continuous
functions have the same underlying functions.  This file transports the positive real
Riesz--Markov theorem across that identification and also packages integration against a finite
measure as a positive continuous functional on `C(X, ℝ)`.
-/

public section

open CompactlySupportedContinuousMap Filter MeasureTheory Set TopologicalSpace
open scoped CompactlySupported ENNReal NNReal

namespace MathlibExt.MeasureTheory

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] in
private theorem continuousMap_integrable_measure (mu : Measure X) [IsFiniteMeasure mu]
    (f : C(X, ℝ)) : Integrable (fun x ↦ f x) mu :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private noncomputable def continuousIntegralLinear (mu : Measure X) [IsFiniteMeasure mu] :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂mu
  map_add' f g := by
    simpa only [ContinuousMap.add_apply] using
      integral_add (continuousMap_integrable_measure mu f)
        (continuousMap_integrable_measure mu g)
  map_smul' c f := by
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply] using
      integral_smul c (fun x ↦ f x)

omit [T2Space X] in
private theorem norm_continuousIntegralLinear_apply_le
    (mu : Measure X) [IsFiniteMeasure mu] (f : C(X, ℝ)) :
    ‖continuousIntegralLinear mu f‖ ≤ mu.real univ * ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := mu) (f := fun x ↦ f x)
    (Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm x)
  simpa [continuousIntegralLinear, mul_comm] using h

/-- Integration against a finite measure, as a positive continuous functional on `C(X, ℝ)`. -/
noncomputable def continuousIntegralPositive (mu : Measure X) [IsFiniteMeasure mu] :
    C(X, ℝ) →P[ℝ] ℝ :=
  { toPositiveLinearMap :=
      { toLinearMap := continuousIntegralLinear mu
        monotone' := by
          intro f g hfg
          exact integral_mono (continuousMap_integrable_measure mu f)
            (continuousMap_integrable_measure mu g) (ContinuousMap.le_def.mp hfg) }
    cont := (continuousIntegralLinear mu).mkContinuous (mu.real univ)
      (norm_continuousIntegralLinear_apply_le mu) |>.cont }

omit [T2Space X] in
/-- The positive functional associated with a finite measure evaluates by integration. -/
@[simp]
theorem continuousIntegralPositive_apply (mu : Measure X) [IsFiniteMeasure mu]
    (f : C(X, ℝ)) :
    continuousIntegralPositive mu f = ∫ x, f x ∂mu := by
  unfold continuousIntegralPositive
  rfl

omit [T2Space X] in
/-- The positive integral functional takes the constant one function to the measure's total mass. -/
@[simp]
theorem continuousIntegralPositive_apply_one (mu : Measure X) [IsFiniteMeasure mu] :
    continuousIntegralPositive mu 1 = mu.real univ := by
  simp [continuousIntegralPositive_apply]

omit [T2Space X] in
/-- Integration of a nonnegative continuous function is monotone in the measure. -/
theorem continuousIntegralPositive_mono_measure {mu nu : Measure X}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] (h : mu ≤ nu)
    {f : C(X, ℝ)} (hf : 0 ≤ f) :
    continuousIntegralPositive mu f ≤ continuousIntegralPositive nu f := by
  rw [continuousIntegralPositive_apply, continuousIntegralPositive_apply]
  exact integral_mono_measure h
    (Filter.Eventually.of_forall (ContinuousMap.le_def.mp hf))
    (continuousMap_integrable_measure nu f)

/-- Restrict a positive continuous functional on `C(X, ℝ)` to compactly supported continuous
functions. -/
noncomputable def compactlySupportedRestriction (P : C(X, ℝ) →P[ℝ] ℝ) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := P f.toContinuousMap
  map_add' f g := by
    change P (f.toContinuousMap + g.toContinuousMap) =
      P f.toContinuousMap + P g.toContinuousMap
    exact map_add P f.toContinuousMap g.toContinuousMap
  map_smul' c f := by
    change P (c • f.toContinuousMap) = c • P f.toContinuousMap
    exact map_smul P c f.toContinuousMap
  monotone' := by
    intro f g hfg
    apply P.monotone'
    exact fun x ↦ hfg x

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
/-- Restricting the positive functional to compactly supported functions preserves its values. -/
@[simp]
theorem compactlySupportedRestriction_apply (P : C(X, ℝ) →P[ℝ] ℝ)
    (f : C_c(X, ℝ)) : compactlySupportedRestriction P f = P f.toContinuousMap := by
  unfold compactlySupportedRestriction
  rfl

/-- The regular measure representing a positive continuous functional on `C(X, ℝ)`. -/
noncomputable def continuousRieszMeasure (P : C(X, ℝ) →P[ℝ] ℝ) : Measure X :=
  RealRMK.rieszMeasure (compactlySupportedRestriction P)

/-- The compact Riesz measure is regular. -/
theorem continuousRieszMeasure_regular (P : C(X, ℝ) →P[ℝ] ℝ) :
    (continuousRieszMeasure P).Regular := by
  unfold continuousRieszMeasure
  infer_instance

/-- The compact Riesz measure is finite. -/
theorem continuousRieszMeasure_finite (P : C(X, ℝ) →P[ℝ] ℝ) :
    IsFiniteMeasure (continuousRieszMeasure P) := by
  unfold continuousRieszMeasure
  infer_instance

/-- The compact Riesz measure represents the original functional on every continuous function. -/
@[simp]
theorem integral_continuousRieszMeasure (P : C(X, ℝ) →P[ℝ] ℝ)
    (f : C(X, ℝ)) :
    ∫ x, f x ∂(continuousRieszMeasure P) = P f := by
  have h := RealRMK.integral_rieszMeasure (compactlySupportedRestriction P)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)
  rw [compactlySupportedRestriction_apply] at h
  change (∫ x, f x ∂(continuousRieszMeasure P)) = P f at h
  exact h

/-- The total mass of the compact Riesz measure is the value of the functional at one. -/
@[simp]
theorem continuousRieszMeasure_real_univ (P : C(X, ℝ) →P[ℝ] ℝ) :
    (continuousRieszMeasure P).real univ = P 1 := by
  simpa using integral_continuousRieszMeasure P (1 : C(X, ℝ))

end

end MathlibExt.MeasureTheory
