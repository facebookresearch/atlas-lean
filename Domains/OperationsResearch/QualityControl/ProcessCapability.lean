/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.StandardizedSelection

import MathlibExt.Probability.Statistics.Measurement.AffineLaws
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Population process capability indices -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace OperationsResearch.QualityControl

/-- The pair `(Cₚ, Cₚₖ)` of population process capability indices for lower and upper
specification limits `L` and `U`, population mean `μ`, and population standard deviation `σ`.
Their statistical interpretation requires `L ≤ U` and `0 < σ`; the formulas are total as
functions on the reals. They do not provide a sampling inference result. See the
NIST/SEMATECH *e-Handbook of Statistical Methods*, §6.1.6. -/
noncomputable def processCapabilityIndices (L U μ σ : ℝ) : ℝ × ℝ :=
  ((U - L) / (6 * σ), min ((U - μ) / (3 * σ)) ((μ - L) / (3 * σ)))

/-- For ordered specification limits `L ≤ U` and positive standard deviation `σ`, the
off-center penalty is `|μ - (L + U) / 2| / (3 * σ)`. In particular `Cₚₖ ≤ Cₚ`, with equality
precisely at the midpoint. Coincident limits give `Cₚ = 0` and `Cₚₖ ≤ 0`. These are
algebraic identities for the population indices, with no normality assumption. -/
theorem processCapabilityIndices_midpoint {L U μ σ : ℝ} (_hLU : L ≤ U) (hσ : 0 < σ) :
    let C := processCapabilityIndices L U μ σ
    let m := (L + U) / 2
    C.2 = C.1 - |μ - m| / (3 * σ) ∧ C.2 ≤ C.1 ∧
      (C.2 = C.1 ↔ μ = m) ∧ (L = U → C.1 = 0 ∧ C.2 ≤ 0) := by
  intro C m
  have hd : 0 < 3 * σ := mul_pos (by norm_num) hσ
  have hmin : min (U - μ) (μ - L) = (U - L) / 2 - |μ - m| := by
    by_cases hμ : μ ≤ m
    · have hn : μ - L ≤ U - μ := by dsimp [m] at hμ; linarith
      rw [min_eq_right hn, abs_of_nonpos (sub_nonpos.mpr hμ)]
      dsimp [m]
      ring
    · have hn : U - μ ≤ μ - L := by dsimp [m] at hμ; linarith
      rw [min_eq_left hn, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hμ))]
      dsimp [m]
      ring
  have hsplit : C.2 = C.1 - |μ - m| / (3 * σ) := by
    change min ((U - μ) / (3 * σ)) ((μ - L) / (3 * σ)) = _
    rw [min_div_div_right hd.le, hmin, sub_div]
    have hw : (U - L) / 2 / (3 * σ) = C.1 := by
      change (U - L) / 2 / (3 * σ) = (U - L) / (6 * σ)
      rw [div_div, show (2 : ℝ) * (3 * σ) = 6 * σ by ring]
    rw [hw]
  have hle : C.2 ≤ C.1 := by
    rw [hsplit]
    exact sub_le_self _ (div_nonneg (abs_nonneg _) hd.le)
  refine ⟨hsplit, hle, ?_, ?_⟩
  · rw [hsplit]
    constructor
    · intro heq
      have he : |μ - m| / (3 * σ) = 0 := by linarith
      have hzero : |μ - m| = 0 := (div_eq_zero_iff.mp he).resolve_right hd.ne'
      exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
    · rintro rfl
      simp
  · intro heq
    have hz : C.1 = 0 := by change (U - L) / (6 * σ) = 0; rw [heq, sub_self, zero_div]
    exact ⟨hz, hle.trans_eq hz⟩

/-- For ordered specification limits `L ≤ U` and positive standard deviation `σ`, an affine
change of units `x ↦ a + b * x` with `0 < b` preserves `Cₚ` and `Cₚₖ` when the mean,
standard deviation, and both limits are expressed in the new units. -/
theorem processCapabilityIndices_affine {L U μ σ : ℝ} (_hLU : L ≤ U) (hσ : 0 < σ)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    processCapabilityIndices (a + b * L) (a + b * U) (a + b * μ) (b * σ) =
      processCapabilityIndices L U μ σ := by
  have hratio (x y c : ℝ) (hc : c ≠ 0) :
      (a + b * x - (a + b * y)) / (c * (b * σ)) = (x - y) / (c * σ) := by
    field_simp [hb.ne', hσ.ne', hc]
    ring
  unfold processCapabilityIndices
  rw [hratio U L 6 (by norm_num), hratio U μ 3 (by norm_num), hratio μ L 3 (by norm_num)]

/-- A positive affine change of units preserves the pass event. For a negative slope it
preserves the pass event with the two transformed endpoints swapped. Reversed original
limits give an empty pass event. -/
theorem processCapability_pass_events {Ω : Type*} (X : Ω → ℝ) (L U a b : ℝ) :
    (0 < b → {ω | L ≤ X ω ∧ X ω ≤ U} =
      {ω | a + b * L ≤ a + b * X ω ∧ a + b * X ω ≤ a + b * U}) ∧
    (b < 0 → {ω | L ≤ X ω ∧ X ω ≤ U} =
      {ω | a + b * U ≤ a + b * X ω ∧ a + b * X ω ≤ a + b * L}) ∧
    (U < L → {ω | L ≤ X ω ∧ X ω ≤ U} = ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hb
    ext ω
    change (L ≤ X ω ∧ X ω ≤ U) ↔
      (a + b * L ≤ a + b * X ω ∧ a + b * X ω ≤ a + b * U)
    simp only [add_le_add_iff_left, mul_le_mul_iff_right₀ hb]
  · intro hb
    ext ω
    change (L ≤ X ω ∧ X ω ≤ U) ↔
      (a + b * U ≤ a + b * X ω ∧ a + b * X ω ≤ a + b * L)
    have horder (x y : ℝ) : b * x ≤ b * y ↔ y ≤ x := by
      rw [← neg_le_neg_iff, ← neg_mul, ← neg_mul, mul_le_mul_iff_right₀ (neg_pos.mpr hb)]
    simp only [add_le_add_iff_left, horder, and_comm]
  · intro hUL
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (not_le_of_gt hUL) (hω.1.trans hω.2)

/-- Let `X` be square-integrable under a probability measure, with positive population
standard deviation `σ`, and let the specification limits satisfy `L ≤ U`. After the affine
recoding `Y = a + b * X` with `0 < b`, the population mean and standard deviation are
`a + b * μ` and `b * σ`, where `μ` is the population mean of `X`. Evaluating the indices
using the recoded moments and limits gives the original pair. -/
theorem processCapabilityIndices_affine_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {L U : ℝ} (hLU : L ≤ U)
    (hσ : 0 < populationSD P X) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    let μ := ∫ ω, X ω ∂P
    let σ := populationSD P X
    let Y := fun ω => a + b * X ω
    (∫ ω, Y ω ∂P) = a + b * μ ∧ populationSD P Y = b * σ ∧
      processCapabilityIndices (a + b * L) (a + b * U) (∫ ω, Y ω ∂P) (populationSD P Y) =
        processCapabilityIndices L U μ σ := by
  intro μ σ Y
  have hY : Y = fun ω => b * X ω + a := by
    funext ω
    exact add_comm a (b * X ω)
  have hm : (∫ ω, Y ω ∂P) = a + b * μ := by
    rw [hY, integral_const_mul_add_const (hX.integrable one_le_two), add_comm a]
  have hs : populationSD P Y = b * σ := by
    rw [hY]
    change Real.sqrt (variance (fun ω => b * X ω + a) P) = b * Real.sqrt (variance X P)
    rw [variance_const_mul_add_const hX.aestronglyMeasurable,
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  exact ⟨hm, hs, by rw [hm, hs]; exact processCapabilityIndices_affine hLU hσ a hb⟩

end OperationsResearch.QualityControl
