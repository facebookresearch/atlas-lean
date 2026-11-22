/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Group.CutoffIndependence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Instances.ZMod

/-! # Consumers and boundary checks for cutoff-independent integration -/

open MeasureTheory Set

set_option autoImplicit false

section Pairings

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) (hT : IsClosed (T : Set G))
  [MeasurableSpace T] [BorelSpace T]
  (μ : Measure G) [μ.IsHaarMeasure]
  (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]

/-- Bounded invariant functions have a cutoff-independent conjugate pairing.
Normalization on the support of the first function suffices, even if the
second function vanishes elsewhere. Integrability is part of the consumer. -/
example (f g : G → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfT : ∀ (t : T) x, f ((t : G) * x) = f x)
    (hgT : ∀ (t : T) x, g ((t : G) * x) = g x)
    (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁ ∧
      ∀ x, f x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂ ∧
      ∀ x, f x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => f x * (starRingEnd ℂ) (g x) * (w₁ x : ℂ)) μ ∧
      (∫ x, f x * (starRingEnd ℂ) (g x) * (w₁ x : ℂ) ∂μ) =
        ∫ x, f x * (starRingEnd ℂ) (g x) * (w₂ x : ℂ) ∂μ := by
  let F : G → ℂ := fun x => f x * (starRingEnd ℂ) (g x)
  have hFm : Measurable F := hfm.mul (Complex.continuous_conj.measurable.comp hgm)
  obtain ⟨A, hA⟩ := hfb
  obtain ⟨B, hB⟩ := hgb
  have hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
    refine ⟨A * B, fun x => ?_⟩
    dsimp [F]
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hA x) (hB x) (norm_nonneg _) ((norm_nonneg (f 1)).trans (hA 1))
  have hFT (t : T) (x : G) : F ((t : G) * x) = F x := by
    simp only [F, hfT, hgT]
  have hsupport (x : G) (hx : F x ≠ 0) : f x ≠ 0 := by
    intro h
    exact hx (by simp [F, h])
  have hnorm₁ (x : G) (hx : F x ≠ 0) := hw₁.2.2.2 x (hsupport x hx)
  have hnorm₂ (x : G) (hx : F x ≠ 0) := hw₂.2.2.2 x (hsupport x hx)
  exact ⟨integrable_mul_of_integral_subgroup_translate_eq_one
      T μ τ hT F hFm hFb hFT w₁ hw₁.1 hw₁.2.1 hw₁.2.2.1 hnorm₁,
    integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
      T hT μ τ F hFm hFb hFT w₁ w₂
      ⟨hw₁.1, hw₁.2.1, hw₁.2.2.1, hnorm₁⟩
      ⟨hw₂.1, hw₂.2.1, hw₂.2.2.1, hnorm₂⟩⟩

/-- A zero invariant function imposes no normalization on either weight.
In particular, the API must not demand subgroup integral one at every point. -/
example (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂) :
    (∫ x, (0 : ℂ) * (w₁ x : ℂ) ∂μ) =
      ∫ x, (0 : ℂ) * (w₂ x : ℂ) ∂μ := by
  apply integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    T hT μ τ (fun _ => 0) measurable_const ⟨0, by simp⟩ (by simp)
  · exact ⟨hw₁.1, hw₁.2.1, hw₁.2.2, fun _ h => (h rfl).elim⟩
  · exact ⟨hw₂.1, hw₂.2.1, hw₂.2.2, fun _ h => (h rfl).elim⟩

end Pairings

namespace TwoOrbits

private abbrev A := Multiplicative (ZMod 2)
private abbrev G := A × A
private abbrev T : Subgroup G := (MonoidHom.snd A A).ker
private def other : A := Multiplicative.ofAdd (1 : ZMod 2)
private theorem other_ne_one : other ≠ (1 : A) := by decide

local instance : MeasurableSpace G := borel G
local instance : BorelSpace G := ⟨rfl⟩
local instance : MeasurableSpace T := borel T
local instance : BorelSpace T := ⟨rfl⟩
local instance : (Measure.count : Measure G).IsHaarMeasure where
  lt_top_of_isCompact _ h := Measure.count_apply_lt_top.mpr h.finite_of_discrete
  toIsMulLeftInvariant := inferInstance
  open_pos _ _ h := Measure.count_ne_zero_iff.mpr h
local instance : (Measure.count : Measure T).IsHaarMeasure where
  lt_top_of_isCompact _ h := Measure.count_apply_lt_top.mpr h.finite_of_discrete
  toIsMulLeftInvariant := inferInstance
  open_pos _ _ h := Measure.count_ne_zero_iff.mpr h

private def firstEquiv : T ≃ A where
  toFun t := t.1.1
  invFun a := ⟨(a, 1), rfl⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact t.property.symm
  right_inv _ := rfl

private noncomputable def weight (a : A) (x : G) : ℝ := if x.1 = a then 1 else 0
private noncomputable def F (x : G) : ℂ := if x.2 = 1 then 2 else 5

private theorem weight_properties (r : A) :
    (∀ x, 0 ≤ weight r x) ∧ Measurable (weight r) ∧ HasCompactSupport (weight r) ∧
      ∀ x : G, ∫ t : T, weight r ((t : G) * x) ∂Measure.count = 1 := by
  refine ⟨fun x => ?_, Measurable.of_discrete, HasCompactSupport.of_compactSpace _, ?_⟩
  · dsimp [weight]
    split_ifs <;> norm_num
  · intro x
    classical
    rw [integral_count, ← firstEquiv.symm.sum_comp]
    change (∑ a : A, if a * x.1 = r then (1 : ℝ) else 0) = 1
    simp_rw [← eq_mul_inv_iff_mul_eq]
    simp

private theorem F_bound (x : G) : ‖F x‖ ≤ 5 := by
  dsimp [F]
  split_ifs <;> norm_num

private theorem F_invariant (t : T) (x : G) : F ((t : G) * x) = F x := by
  have ht : (t : G).2 = 1 := t.property
  simp [F, ht]

private theorem integral_count_pair (f : G → ℂ) :
    ∫ x, f x ∂Measure.count =
      (f (1, 1) + f (1, other)) + (f (other, 1) + f (other, other)) := by
  rw [integral_count]
  have hu : (Finset.univ : Finset G) =
      {(1, 1), (1, other), (other, 1), (other, other)} := by decide
  rw [hu]
  simp [other_ne_one, Ne.symm other_ne_one, add_assoc]

/-- Two different cutoffs on `(ℤ/2ℤ)²` give the same nonzero integral for a
nonconstant function on the two orbits. The value seven rules out a vacuous
equality of nonintegrable Bochner integrals, and the integrability API is used. -/
example : weight 1 ≠ weight other ∧
    Integrable (fun x => F x * (weight 1 x : ℂ)) Measure.count ∧
    (∫ x, F x * (weight 1 x : ℂ) ∂Measure.count) = 7 ∧
    (∫ x, F x * (weight other x : ℂ) ∂Measure.count) = 7 := by
  rcases weight_properties 1 with ⟨hn₁, hm₁, hc₁, hi₁⟩
  rcases weight_properties other with ⟨hn₂, hm₂, hc₂, hi₂⟩
  have hv : (∫ x, F x * (weight 1 x : ℂ) ∂Measure.count) = 7 := by
    rw [integral_count_pair]
    norm_num [F, weight, other_ne_one, Ne.symm other_ne_one]
  have heq := integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    T (isClosed_discrete _) Measure.count Measure.count F Measurable.of_discrete
    ⟨5, F_bound⟩ F_invariant (weight 1) (weight other)
    ⟨hn₁, hm₁, hc₁, fun x _ => hi₁ x⟩ ⟨hn₂, hm₂, hc₂, fun x _ => hi₂ x⟩
  refine ⟨?_, integrable_mul_of_integral_subgroup_translate_eq_one
    T Measure.count Measure.count (isClosed_discrete _) F Measurable.of_discrete
    ⟨5, F_bound⟩ F_invariant (weight 1) hn₁ hm₁ hc₁ (fun x _ => hi₁ x),
    hv, heq.symm.trans hv⟩
  intro h
  have h1 := congrFun h (1, 1)
  norm_num [weight, Ne.symm other_ne_one] at h1

/-- Dropping invariance really changes the answer, even for finite groups,
nonnegative normalized cutoffs, and a bounded measurable integrand. -/
example : ∃ f : G → ℂ,
    Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
    ¬ (∀ (t : T) x, f ((t : G) * x) = f x) ∧
    (∫ x, f x * (weight 1 x : ℂ) ∂Measure.count) = 2 ∧
    (∫ x, f x * (weight other x : ℂ) ∂Measure.count) = 0 := by
  let f : G → ℂ := fun x => if x.1 = 1 then 1 else 0
  refine ⟨f, Measurable.of_discrete, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp [f]
    split_ifs <;> norm_num
  · intro h
    have h1 := h ⟨(other, 1), rfl⟩ 1
    norm_num [f, other_ne_one] at h1
  · rw [integral_count_pair]
    norm_num [f, weight, other_ne_one, Ne.symm other_ne_one]
  · rw [integral_count_pair]
    norm_num [f, weight, other_ne_one, Ne.symm other_ne_one]

end TwoOrbits
