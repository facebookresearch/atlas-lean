/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Group.ActionCutoff
import MathlibExt.MeasureTheory.Group.ActionCutoffWithDensity
import Mathlib.Topology.Instances.ZMod

/-! # Distinct densities, Banach observables and exceptional null orbits -/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace CutoffTransportTest

private abbrev C2 := Multiplicative (ZMod 2)
private def other : C2 := Multiplicative.ofAdd (1 : ZMod 2)
private theorem other_ne_one : other ≠ (1 : C2) := by decide
private theorem cases_C2 (a : C2) : a = 1 ∨ a = other := by revert a; decide
private theorem univ_C2 : (Finset.univ : Finset C2) = {1, other} := by decide
private theorem other_sq : other * other = (1 : C2) := by decide

local instance : MeasurableSpace C2 := borel C2
local instance : BorelSpace C2 := ⟨rfl⟩

section ProductAction

variable {Y : Type*}

local instance (priority := 2000) leftSMul : SMul C2 (C2 × Y) :=
  ⟨fun a p => (a * p.1, p.2)⟩

local instance (priority := 2000) : MulAction C2 (C2 × Y) where
  one_smul p := by change ((1 : C2) * p.1, p.2) = p; simp
  mul_smul a b p := by
    change ((a * b) * p.1, p.2) = (a * (b * p.1), p.2)
    rw [mul_assoc]

private theorem fst_smul (a : C2) (p : C2 × Y) : (a • p).1 = a * p.1 := rfl
private theorem snd_smul (a : C2) (p : C2 × Y) : (a • p).2 = p.2 := rfl

private noncomputable def weight (r : C2) (p : C2 × Y) : ℝ≥0∞ :=
  if p.1 = r then 1 else 0

private theorem finite_weight (r : C2) (p : C2 × Y) : weight r p ≠ ∞ := by
  simp only [weight]
  split_ifs <;> simp

private theorem normalized (r : C2) (p : C2 × Y) :
    ∫⁻ a : C2, weight r (a • p) ∂Measure.count = 1 := by
  rw [lintegral_count, tsum_fintype, univ_C2, Finset.sum_pair (Ne.symm other_ne_one)]
  rcases cases_C2 r with rfl | rfl <;> rcases cases_C2 p.1 with hp | hp <;>
    simp [weight, fst_smul, hp, other_sq, other_ne_one, Ne.symm other_ne_one]

/-- A quotient observable with an arbitrary real Banach target has the same
integral for two disjointly supported densities. It need not be constant on
all of the ambient space. -/
theorem banach_finite_quotient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : C2 → E) :
    Integrable (fun p : C2 × C2 => F p.2) ((Measure.count).withDensity (weight other)) ∧
      (∫ p : C2 × C2, F p.2 ∂(Measure.count).withDensity (weight other)) = F 1 + F other := by
  have hm (r : C2) : Measurable (weight r : C2 × C2 → ℝ≥0∞) := Measurable.of_discrete
  have hμ (a : C2) : MeasurePreserving (fun p : C2 × C2 => a • p)
      Measure.count Measure.count := by
    change MeasurePreserving (fun p : C2 × C2 => (a * p.1, p.2))
      Measure.count Measure.count
    simpa only [Prod.mul_def, one_mul] using
      (measurePreserving_mul_left (Measure.count : Measure (C2 × C2)) (a, 1))
  have hi : Integrable (fun p : C2 × C2 => F p.2) ((Measure.count).withDensity (weight 1)) := by
    rw [integrable_withDensity_iff_integrable_smul' (hm 1)
      (ae_of_all _ fun p => lt_top_iff_ne_top.mpr (finite_weight 1 p))]
    exact integrable_count_iff.mpr Summable.of_finite
  have h := integrable_and_integral_withDensity_eq_of_normalized_smul
    (Measure.count : Measure C2) (Measure.count : Measure (C2 × C2))
    Measurable.of_discrete hμ (hm 1) (hm other) (normalized 1) (normalized other)
    (finite_weight 1) (finite_weight other) (fun _ _ => rfl) hi
  refine ⟨h.1, h.2.trans ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul (hm 1)
    (ae_of_all _ fun p => lt_top_iff_ne_top.mpr (finite_weight 1 p)), integral_count]
  have hu : (Finset.univ : Finset (C2 × C2)) =
      {(1, 1), (1, other), (other, 1), (other, other)} := by decide
  rw [hu]
  simp [weight, other_ne_one, Ne.symm other_ne_one]

/-- A concrete R² target, rather than a complex-valued specialization. -/
theorem vector_integral :
    (∫ p : C2 × C2, (if p.2 = 1 then (2, -3) else (7, 5) : ℝ × ℝ)
      ∂(Measure.count).withDensity (weight other)) = (9, 2) := by
  have h := (banach_finite_quotient (fun y => if y = 1 then (2, -3) else (7, 5) : C2 → ℝ × ℝ)).2
  norm_num [other_ne_one] at h ⊢
  exact h

/-- The two normalized densities really have disjoint supports. -/
theorem disjoint_weights (p : C2 × C2) : weight 1 p * weight other p = 0 := by
  rcases cases_C2 p.1 with hp | hp <;>
    simp [weight, hp, other_ne_one, Ne.symm other_ne_one]

/-- Dropping invariance makes normalized weights select different values. -/
theorem invariance_is_needed :
    (∫⁻ p : C2 × C2, weight 1 p * weight 1 p ∂Measure.count) ≠
      ∫⁻ p : C2 × C2, weight 1 p * weight other p ∂Measure.count := by
  have hu : (Finset.univ : Finset (C2 × C2)) =
      {(1, 1), (1, other), (other, 1), (other, other)} := by decide
  simp [lintegral_count, tsum_fintype, hu, weight, other_ne_one, Ne.symm other_ne_one]

private noncomputable def nullOrbitMeasure : Measure (C2 × Bool) :=
  (Measure.count : Measure C2).prod (Measure.dirac false)

private noncomputable def aeWeight (r : C2) (p : C2 × Bool) : ℝ≥0∞ :=
  if p.2 then ∞ else weight r p

private theorem ae_normalized (r : C2) :
    ∀ᵐ p ∂nullOrbitMeasure, ∫⁻ a : C2, aeWeight r (a • p) ∂Measure.count = 1 := by
  have hp : ∀ᵐ p : C2 × Bool ∂nullOrbitMeasure, p.2 = false :=
    (Measure.quasiMeasurePreserving_snd (μ := (Measure.count : Measure C2))
      (ν := Measure.dirac false)).ae (show ∀ᵐ b ∂Measure.dirac false, b = false by simp)
  filter_upwards [hp] with p hp
  simpa only [aeWeight, snd_smul, hp, Bool.false_eq_true, ↓reduceIte] using normalized r p

/-- Normalization genuinely fails on a null orbit; it is not a pointwise
example restated with an a.e. quantifier. Infinite weights are permitted here. -/
theorem exceptional_orbit :
    (∫⁻ a : C2, aeWeight 1 (a • (1, true)) ∂Measure.count) ≠ 1 := by
  simp [lintegral_count, tsum_fintype, univ_C2, aeWeight, Ne.symm other_ne_one]

/-- A.e.-normalized cutoffs transport nonnegative observables even with
infinite weights on the exceptional null orbit. The observable may be infinity. -/
theorem ae_cutoff_integral (c : ℝ≥0∞) :
    (∫⁻ p, c * aeWeight 1 p ∂nullOrbitMeasure) =
      ∫⁻ p, c * aeWeight other p ∂nullOrbitMeasure := by
  let : SFinite nullOrbitMeasure := by unfold nullOrbitMeasure; infer_instance
  have hμ (a : C2) : MeasurePreserving (fun p : C2 × Bool => a • p)
      nullOrbitMeasure nullOrbitMeasure :=
    (measurePreserving_mul_left (Measure.count : Measure C2) a).prod
      (MeasurePreserving.id (Measure.dirac false))
  exact lintegral_mul_eq_of_ae_normalized_smul (Measure.count : Measure C2)
    nullOrbitMeasure Measurable.of_discrete hμ measurable_const.aemeasurable (fun _ _ => rfl)
    Measurable.of_discrete Measurable.of_discrete
    ((ae_normalized 1).mono fun _ h _ => h) ((ae_normalized other).mono fun _ h _ => h)

/-- The common value is not forced to zero by the exceptional infinite density. -/
theorem ae_cutoff_value (c : ℝ≥0∞) :
    (∫⁻ p, c * aeWeight 1 p ∂nullOrbitMeasure) = c := by
  rw [nullOrbitMeasure, lintegral_prod _ Measurable.of_discrete.aemeasurable]
  simp [aeWeight, weight, lintegral_count, tsum_fintype, univ_C2, Ne.symm other_ne_one]

/-- Infinite observables retain an infinite, rather than totalized-zero, integral. -/
theorem infinite_observable :
    (∫⁻ p, (∞ : ℝ≥0∞) * aeWeight other p ∂nullOrbitMeasure) = ∞ :=
  (ae_cutoff_integral ∞).symm.trans (ae_cutoff_value ∞)

/-- Zero times an infinite weight remains zero, including on the null orbit. -/
theorem zero_observable : (∫⁻ p, (0 : ℝ≥0∞) * aeWeight 1 p ∂nullOrbitMeasure) = 0 := by simp

end ProductAction

end CutoffTransportTest
