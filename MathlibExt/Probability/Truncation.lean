/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovThreeSeries

/-!
# Properties of the canonical truncation of random variables

This module extends `ProbabilityTheory.KolmogorovThreeSeries.truncatedRV`,
the closed-cutoff truncation `Xₙ · 1_{|Xₙ| ≤ A}` used by the three-series API.
Its scalar specialization, composition, bounded-convergence, `MemLp`,
integrability, variance and mean properties all use that same definition.

The scalar `truncationFun` is an abbreviation of canonical truncation applied
to the identity sequence. Measurability, independence, inside-cutoff identities
and absolute bounds reuse the existing canonical lemmas. Single-index
measurability needs only measurability of the selected variable. The `MemLp`
and integrability results use finite measures; the variance and mean bounds
use probability measures. Thresholds may be zero or negative.

## Source

The truncation helpers come from
`v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean`:
`truncatedRV_eq_comp`, `measurable_truncation_fun`,
`iIndepFun_truncatedRV`, `abs_truncatedRV_le`,
`truncated_indicator_eq_of_bdd`, `truncatedRV_eq_of_bdd`, and
`ae_tendsto_truncatedRV_of_bdd`. The canonical definition and matching
properties are supplied by `MathlibExt.Probability.KolmogorovThreeSeries`.
No second sequence truncation definition is introduced here.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

noncomputable section

namespace ProbabilityTheory.KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Scalar truncation is canonical truncation of the identity sequence. -/
abbrev truncationFun (A : ℝ) : ℝ → ℝ :=
  truncatedRV (fun _ => id) A 0

omit [MeasurableSpace Ω] in
/-- Truncation of a value strictly outside the closed band is zero. -/
theorem truncatedRV_eq_zero_of_abs_gt {X : ℕ → Ω → ℝ} {A : ℝ} {n : ℕ} {ω : Ω}
    (h : A < |X n ω|) : truncatedRV X A n ω = 0 := by
  rw [truncatedRV_apply, ite_eq_right (not_le.mpr h)]

omit [MeasurableSpace Ω] in
/-- Canonical truncation preserves nonnegativity. -/
theorem truncatedRV_nonneg_of_nonneg {X : ℕ → Ω → ℝ} {A : ℝ} {n : ℕ} {ω : Ω}
    (h : 0 ≤ X n ω) : 0 ≤ truncatedRV X A n ω := by
  rw [truncatedRV_apply]
  split_ifs
  · exact h
  · exact le_rfl

/-- Scalar truncation fixes values inside or on the cutoff. -/
theorem truncationFun_eq_self_of_abs_le {A x : ℝ} (hx : |x| ≤ A) :
    truncationFun A x = x :=
  truncatedRV_eq_of_abs_le hx

/-- Scalar truncation kills values strictly outside the cutoff. -/
theorem truncationFun_eq_zero_of_abs_gt {A x : ℝ} (hx : A < |x|) :
    truncationFun A x = 0 :=
  truncatedRV_eq_zero_of_abs_gt hx

/-- Scalar truncation preserves nonnegativity. -/
theorem truncationFun_nonneg_of_nonneg {A x : ℝ} (hx : 0 ≤ x) :
    0 ≤ truncationFun A x :=
  truncatedRV_nonneg_of_nonneg hx

omit [MeasurableSpace Ω] in
/-- Canonical truncation factors through its scalar specialization. -/
theorem truncatedRV_eq_comp (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) :
    truncatedRV X A n = truncationFun A ∘ X n := by
  funext ω
  simp only [truncationFun, truncatedRV_apply, Function.comp_apply, id_eq]

/-- The scalar specialization of canonical truncation is measurable. -/
theorem measurable_truncationFun (A : ℝ) : Measurable (truncationFun A) :=
  measurable_truncatedRV (fun _ => measurable_id) A 0

/-- Canonical truncation needs measurability only of the selected variable. -/
theorem measurable_truncatedRV_of_measurable {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    Measurable (truncatedRV X A n) :=
  measurable_truncatedRV (X := fun _ => X n) (fun _ => hX) A 0

omit [MeasurableSpace Ω] in
/-- A family bounded by the cutoff is unchanged by canonical truncation. -/
theorem truncatedRV_eq_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY : ∀ n ω, |Y n ω| ≤ A) (n : ℕ) :
    truncatedRV Y A n = Y n := by
  funext ω
  exact truncatedRV_eq_of_abs_le (hY n ω)

/-- A uniformly bounded family keeps its almost-sure partial-sum limit under
canonical truncation, on the same measure. -/
theorem ae_tendsto_truncatedRV_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY : ∀ n ω, |Y n ω| ≤ A)
    (hY_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => Y i ω)) atTop (nhds (S ω))) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncatedRV Y A i ω)) atTop (nhds (S ω)) :=
  ae_tendsto_of_ae_eventually_eq_and_ae_tendsto
    (Eventually.of_forall fun ω => Eventually.of_forall fun n =>
      (truncatedRV_eq_of_abs_le (hY n ω)).symm) hY_tend

/-- Canonical truncation is in every `Lᵖ` on a finite measure space. -/
theorem memLp_truncatedRV [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) (p : ℝ≥0∞) :
    MemLp (truncatedRV X A n) p μ :=
  MemLp.of_bound (measurable_truncatedRV_of_measurable n hX A).aestronglyMeasurable |A|
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_truncatedRV_le_abs A n ω)

/-- Canonical truncation is integrable on a finite measure space. -/
theorem integrable_truncatedRV [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    Integrable (truncatedRV X A n) μ :=
  (memLp_truncatedRV n hX A 1).integrable le_rfl

/-- The variance of canonical truncation is at most `A²`. -/
theorem variance_truncatedRV_le [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    variance (truncatedRV X A n) μ ≤ A ^ 2 := by
  have hmem : ∀ᵐ ω ∂μ, truncatedRV X A n ω ∈ Set.Icc (-|A|) |A| := by
    filter_upwards with ω
    exact abs_le.mp (abs_truncatedRV_le_abs A n ω)
  have hbound := variance_le_sq_of_bounded (a := -|A|) (b := |A|) hmem
    (measurable_truncatedRV_of_measurable n hX A).aemeasurable
  calc variance (truncatedRV X A n) μ ≤ ((|A| - -|A|) / 2) ^ 2 := hbound
    _ = A ^ 2 := by
        rw [sub_neg_eq_add, ← two_mul, mul_div_cancel_left₀ _ (two_ne_zero), sq_abs]

/-- The absolute mean of canonical truncation is at most `|A|`. -/
theorem abs_integral_truncatedRV_le [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    |∫ ω, truncatedRV X A n ω ∂μ| ≤ |A| := by
  calc |∫ ω, truncatedRV X A n ω ∂μ| ≤ ∫ ω, |truncatedRV X A n ω| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, |A| ∂μ :=
        integral_mono_ae (integrable_truncatedRV n hX A).abs (integrable_const _)
          (Filter.Eventually.of_forall fun ω => abs_truncatedRV_le_abs A n ω)
    _ = |A| := by simp

end ProbabilityTheory.KolmogorovThreeSeries

end
