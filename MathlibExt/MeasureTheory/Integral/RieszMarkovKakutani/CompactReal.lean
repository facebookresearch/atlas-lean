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
# Positive Riesz representation on compact Hausdorff spaces

On a compact Borel space, integration against a finite measure gives the positive bounded
functional `f ↦ ∫ f dμ` on `C(X,ℝ)`, with value `μ(X)` at one.

When the space is Hausdorff, a positive bounded functional `P` is represented by a finite
regular measure `μ_P`, satisfying `∫ f dμ_P=P(f)` and `μ_P(X)=P(1)`. Restriction to
compact-support continuous functions is pointwise and also makes sense on general topological
spaces.
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

/-- **Positive bounded integration functional on compact continuous functions.** Let `X` be a
compact topological space with its Borel measurable structure. for a finite measure `μ`,
`continuousIntegralPositive μ : C(X,ℝ) → ℝ` sends `f` to `∫ f dμ` and is positive and
continuous. Hausdorffness is not required. -/
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
/-- **Value of the positive continuous integral functional.** Let `X` be a compact topological
space with its Borel measurable structure. for finite `μ` and `f∈C(X,ℝ)`,
`continuousIntegralPositive μ f=∫ f dμ`, without a Hausdorff assumption. -/
@[simp]
theorem continuousIntegralPositive_apply (mu : Measure X) [IsFiniteMeasure mu]
    (f : C(X, ℝ)) :
    continuousIntegralPositive mu f = ∫ x, f x ∂mu := by
  unfold continuousIntegralPositive
  rfl

omit [T2Space X] in
/-- **Total mass of a positive integral functional.** Let `X` be a compact topological space
with its Borel measurable structure. for finite `μ`, `continuousIntegralPositive μ
1=μ.real(X)`. -/
@[simp]
theorem continuousIntegralPositive_apply_one (mu : Measure X) [IsFiniteMeasure mu] :
    continuousIntegralPositive mu 1 = mu.real univ := by
  simp [continuousIntegralPositive_apply]

omit [T2Space X] in
/-- **Monotonicity of nonnegative continuous integration in the measure.** Let `X` be a
compact topological space with its Borel measurable structure. if finite measures `μ≤ν`
and `f∈C(X,ℝ)` satisfies `f≥0`, then `∫ f dμ≤∫ f dν`. -/
theorem continuousIntegralPositive_mono_measure {mu nu : Measure X}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] (h : mu ≤ nu)
    {f : C(X, ℝ)} (hf : 0 ≤ f) :
    continuousIntegralPositive mu f ≤ continuousIntegralPositive nu f := by
  rw [continuousIntegralPositive_apply, continuousIntegralPositive_apply]
  exact integral_mono_measure h
    (Filter.Eventually.of_forall (ContinuousMap.le_def.mp hf))
    (continuousMap_integrable_measure nu f)

/-- **Positive functional restricted to compact-support functions.** For a topological space
`X` and positive continuous real-linear `P : C(X,ℝ) → ℝ`, `compactlySupportedRestriction
P` sends `f∈C_c(X,ℝ)` to `P(f.toContinuousMap)`. -/
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
/-- **Value of a compact-support positive-functional restriction.** For a topological space
`X`, positive continuous real-linear `P : C(X,ℝ) → ℝ` and `f∈C_c(X,ℝ)`,
`compactlySupportedRestriction P f=P(f.toContinuousMap)`. -/
@[simp]
theorem compactlySupportedRestriction_apply (P : C(X, ℝ) →P[ℝ] ℝ)
    (f : C_c(X, ℝ)) : compactlySupportedRestriction P f = P f.toContinuousMap := by
  unfold compactlySupportedRestriction
  rfl

/-- **Finite regular representing measure of a positive continuous functional.** Let `X` be a
compact Hausdorff space with its Borel measurable structure. for positive bounded `P :
C(X,ℝ) → ℝ`, `continuousRieszMeasure P=μ_P` satisfies `∫ f dμ_P=P(f)` for every continuous
real `f`. -/
noncomputable def continuousRieszMeasure (P : C(X, ℝ) →P[ℝ] ℝ) : Measure X :=
  RealRMK.rieszMeasure (compactlySupportedRestriction P)

/-- **Regularity of the positive compact Riesz measure.** Let `X` be a compact Hausdorff space
with its Borel measurable structure. for positive bounded `P`, the measure
`continuousRieszMeasure P` is regular. -/
theorem continuousRieszMeasure_regular (P : C(X, ℝ) →P[ℝ] ℝ) :
    (continuousRieszMeasure P).Regular := by
  unfold continuousRieszMeasure
  infer_instance

/-- **Finiteness of the positive compact Riesz measure.** Let `X` be a compact Hausdorff space
with its Borel measurable structure. for positive bounded `P`, `continuousRieszMeasure P`
is finite. -/
theorem continuousRieszMeasure_finite (P : C(X, ℝ) →P[ℝ] ℝ) :
    IsFiniteMeasure (continuousRieszMeasure P) := by
  unfold continuousRieszMeasure
  infer_instance

/-- **Continuous integral representation of a positive compact functional.** Let `X` be a
compact Hausdorff space with its Borel measurable structure. for positive bounded `P` and
`f∈C(X,ℝ)`, `∫ f d(continuousRieszMeasure P)=P(f)`. -/
@[simp]
theorem integral_continuousRieszMeasure (P : C(X, ℝ) →P[ℝ] ℝ)
    (f : C(X, ℝ)) :
    ∫ x, f x ∂(continuousRieszMeasure P) = P f := by
  have h := RealRMK.integral_rieszMeasure (compactlySupportedRestriction P)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)
  rw [compactlySupportedRestriction_apply] at h
  change (∫ x, f x ∂(continuousRieszMeasure P)) = P f at h
  exact h

/-- **Positive Riesz total mass equals the functional at one.** Let `X` be a compact Hausdorff
space with its Borel measurable structure. for positive bounded `P`,
`(continuousRieszMeasure P).real(X)=P(1)`. -/
@[simp]
theorem continuousRieszMeasure_real_univ (P : C(X, ℝ) →P[ℝ] ℝ) :
    (continuousRieszMeasure P).real univ = P 1 := by
  simpa using integral_continuousRieszMeasure P (1 : C(X, ℝ))

end

end MathlibExt.MeasureTheory
