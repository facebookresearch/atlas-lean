/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy

/-!
# Approximate differential privacy

Event privacy for normalized discrete PMFs and supplied ordered adjacency.
The bounded-test characterization charges delta once. Randomized
postprocessing preserves both budgets; adaptive two-stage composition
releases the full transcript with additive budgets.

Dwork and Roth (2014), Definition 2.4, Proposition 2.1, Theorem 3.16 and
Appendix B. The bounded-test interface is derived from atomwise excess,
not the book's setwise positive-part expression, which is not a measure.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

open scoped ENNReal

/-- Approximate event privacy, with global nonnegative real budgets.
All subsets are events; delta is allowed to exceed one. -/
def IsApproxDP {D A : Type*} (M : D → PMF A)
    (adj : D → D → Prop) (ε δ : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ ∀ d d', adj d d' → ∀ s : Set A,
    (M d).toOuterMeasure s ≤
      ENNReal.ofReal (Real.exp ε) * (M d').toOuterMeasure s +
        ENNReal.ofReal δ

/-- Zero-delta privacy is exactly the existing pure-DP predicate. -/
theorem isApproxDP_zero_iff {D A : Type*} {M : D → PMF A}
    {adj : D → D → Prop} {ε : ℝ} :
    IsApproxDP M adj ε 0 ↔ IsDP M adj ε := by
  rw [isDP_iff_isDPEvent]
  simp only [IsApproxDP, IsDPEvent, le_refl, ENNReal.ofReal_zero,
    add_zero, true_and]

private theorem event_le_one {A : Type*} (p : PMF A) (s : Set A) :
    p.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self s p a

private theorem excess_le {A : Type*} (p q : PMF A)
    {c δ : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ s : Set A, p.toOuterMeasure s ≤ c * q.toOuterMeasure s + δ) :
    (∑' a, (p a - c * q a)) ≤ δ := by
  classical
  let s : Set A := {a | c * q a < p a}
  have heq : (∑' a, (p a - c * q a)) + c * q.toOuterMeasure s =
      p.toOuterMeasure s := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
      ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases ha : a ∈ s
    · simpa only [Set.indicator_of_mem ha] using
        tsub_add_cancel_of_le (le_of_lt ha)
    · have hle : p a ≤ c * q a := le_of_not_gt ha
      simp only [Set.indicator_of_notMem ha, mul_zero,
        tsub_eq_zero_of_le hle, add_zero]
  have hfin : c * q.toOuterMeasure s ≠ ⊤ :=
    ENNReal.mul_ne_top hc (ne_of_lt ((event_le_one q s).trans_lt
      ENNReal.one_lt_top))
  apply (ENNReal.add_le_add_iff_right hfin).mp
  rw [heq, add_comm δ]
  exact h s

private theorem test_le {A : Type*} (p q : PMF A)
    {c δ : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ s : Set A, p.toOuterMeasure s ≤ c * q.toOuterMeasure s + δ)
    (f : A → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    (∑' a, p a * f a) ≤ c * (∑' a, q a * f a) + δ := by
  calc
    (∑' a, p a * f a) ≤
        ∑' a, (c * (q a * f a) + (p a - c * q a)) := by
      apply ENNReal.tsum_le_tsum
      intro a
      calc
        p a * f a ≤ (c * q a + (p a - c * q a)) * f a :=
          mul_le_mul' le_add_tsub le_rfl
        _ = c * (q a * f a) + (p a - c * q a) * f a := by
          rw [add_mul, mul_assoc]
        _ ≤ c * (q a * f a) + (p a - c * q a) :=
          add_le_add le_rfl (mul_le_of_le_one_right' (hf a))
    _ = c * (∑' a, q a * f a) + ∑' a, (p a - c * q a) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ c * (∑' a, q a * f a) + δ :=
      add_le_add le_rfl (excess_le p q hc h)

/-- Event privacy is equivalent to privacy for every test valued in [0,1].
The additive delta occurs once, outside the complete expectation. -/
theorem isApproxDP_iff_bounded_test {D A : Type*} {M : D → PMF A}
    {adj : D → D → Prop} {ε δ : ℝ} :
    IsApproxDP M adj ε δ ↔
      (0 ≤ ε ∧ 0 ≤ δ ∧ ∀ d d', adj d d' →
        ∀ f : A → ℝ≥0∞, (∀ a, f a ≤ 1) →
          (∑' a, M d a * f a) ≤
            ENNReal.ofReal (Real.exp ε) * (∑' a, M d' a * f a) +
              ENNReal.ofReal δ) := by
  classical
  constructor
  · rintro ⟨hε, hδ, h⟩
    exact ⟨hε, hδ, fun d d' ha f hf =>
      test_le (M d) (M d') ENNReal.ofReal_ne_top (h d d' ha) f hf⟩
  · rintro ⟨hε, hδ, h⟩
    refine ⟨hε, hδ, fun d d' ha s => ?_⟩
    have hi : ∀ p : PMF A,
        (∑' a, p a * s.indicator (fun _ => 1) a) = p.toOuterMeasure s := by
      intro p
      rw [PMF.toOuterMeasure_apply]
      apply tsum_congr
      intro a
      by_cases ha : a ∈ s <;> simp [ha]
    simpa only [hi] using h d d' ha (s.indicator fun _ => 1)
      (fun a => by by_cases ha : a ∈ s <;> simp [ha])

/-- A database-independent randomized kernel preserves both budgets. -/
theorem isApproxDP_bind {D A B : Type*} {M : D → PMF A}
    {adj : D → D → Prop} {ε δ : ℝ} (hM : IsApproxDP M adj ε δ)
    (k : A → PMF B) : IsApproxDP (fun d => (M d).bind k) adj ε δ := by
  refine ⟨hM.1, hM.2.1, fun d d' ha s => ?_⟩
  simp only [PMF.toOuterMeasure_bind_apply]
  exact (isApproxDP_iff_bounded_test.mp hM).2.2 d d' ha
    (fun a => (k a).toOuterMeasure s) (fun a => event_le_one (k a) s)

private theorem joint_event {A B : Type*} (p : PMF A) (k : A → PMF B)
    (s : Set (A × B)) :
    (p.bind fun a => (k a).bind fun b => PMF.pure (a, b)).toOuterMeasure s =
      ∑' a, p a * (k a).toOuterMeasure {b | (a, b) ∈ s} := by
  rw [PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro a
  congr 1
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro b
  by_cases h : (a, b) ∈ s <;>
    simp [PMF.toOuterMeasure_pure_apply, h]

private theorem capped_test_le {A : Type*} (p : PMF A)
    (f g : A → ℝ≥0∞) {δ : ℝ≥0∞}
    (hf : ∀ a, f a ≤ 1) (h : ∀ a, f a ≤ g a + δ) :
    (∑' a, p a * f a) ≤ (∑' a, p a * min (g a) 1) + δ := by
  have hcap : ∀ a, f a ≤ min (g a) 1 + δ := by
    intro a
    by_cases ha : g a ≤ 1
    · simpa only [min_eq_left ha] using h a
    · rw [min_eq_right (le_of_not_ge ha)]
      exact (hf a).trans le_self_add
  calc
    (∑' a, p a * f a) ≤ ∑' a, p a * (min (g a) 1 + δ) :=
      ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (hcap a)
    _ = (∑' a, p a * min (g a) 1) + δ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- Adaptive two-stage composition preserves the full ordered transcript.
The stage budgets are uniform and add without exponential delta inflation. -/
theorem isApproxDP_comp_bind_pair {D A B : Type*} {M : D → PMF A}
    {K : A → D → PMF B} {adj : D → D → Prop} {ε₁ δ₁ ε₂ δ₂ : ℝ}
    (hM : IsApproxDP M adj ε₁ δ₁) (hε₂ : 0 ≤ ε₂) (hδ₂ : 0 ≤ δ₂)
    (hK : ∀ a, IsApproxDP (K a) adj ε₂ δ₂) :
    IsApproxDP (fun d => (M d).bind fun a =>
      (K a d).bind fun b => PMF.pure (a, b)) adj (ε₁ + ε₂) (δ₁ + δ₂) := by
  refine ⟨add_nonneg hM.1 hε₂, add_nonneg hM.2.1 hδ₂, ?_⟩
  intro d d' ha s
  let c₂ := ENNReal.ofReal (Real.exp ε₂)
  let f := fun a => (K a d).toOuterMeasure {b | (a, b) ∈ s}
  let g := fun a => (K a d').toOuterMeasure {b | (a, b) ∈ s}
  have hc := capped_test_le (M d) f (fun a => c₂ * g a)
    (fun a => event_le_one _ _) (fun a => (hK a).2.2 d d' ha _)
  have ht := (isApproxDP_iff_bounded_test.mp hM).2.2 d d' ha
    (fun a => min (c₂ * g a) 1) (fun a => min_le_right _ _)
  have hg : (∑' a, M d' a * min (c₂ * g a) 1) ≤
      c₂ * ∑' a, M d' a * g a := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro a
    exact (mul_le_mul' le_rfl (min_le_left _ _)).trans_eq
      (mul_left_comm _ _ _)
  rw [joint_event, joint_event, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_add hM.2.1 hδ₂]
  exact (hc.trans (add_le_add ht le_rfl)).trans
    ((add_le_add (add_le_add (mul_le_mul' le_rfl hg) le_rfl) le_rfl).trans_eq
      (by simp only [c₂, g, mul_assoc, add_assoc]))

end CSLibExt.Privacy.DifferentialPrivacy
