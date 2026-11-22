/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.GumbelTail
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Shared `Exp(1)` ladder fixture for the score-significance tests

A nontrivial `LadderInput`: i.i.d. `Exp(1)` excursion heights on the product space
`ℕ → ℝ`, one excursion per step (`A = 1`), `Mₙ = max_{i ≤ n} ω i` the running maximum, and the
exponential tail `(1 - F t) e^{t} → 1`. Used by the `GumbelTail` and `Calibration` tests.

Source receipt: the declarations below were moved verbatim from
`CSLibExtTest/Bioinformatics/Alignment/ScoreSignificance/GumbelTail.lean` and
`CSLibExtTest/Bioinformatics/Alignment/ScoreSignificance/Calibration.lean`, where they were
duplicated. They reuse `LadderInput` and `tendsto_tail_of_eq_exp` from
`CSLibExt.Bioinformatics.Alignment.ScoreSignificance.GumbelTail`, and `expMeasure`,
`cdf_expMeasure_eq`, `Measure.infinitePi` and `iIndepFun_infinitePi` from Mathlib. Nothing new
is proved here.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- I.i.d. `Exp(1)` coordinates. -/
noncomputable abbrev Pexp : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => expMeasure 1

/-- The running maximum `max_{i ≤ n} ω i`. -/
noncomputable def runMax (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ ω

/-- One `Exp(1)` excursion per step: `Y i ω = ω i`, `N n = n`, `A = 1`, `F = cdf Exp(1)`. -/
noncomputable def expLadder : LadderInput Pexp runMax where
  Y i ω := ω i
  N n _ := n
  F t := cdf (expMeasure 1) t
  A := 1
  A_pos := one_pos
  measurable_Y i := measurable_pi_apply i
  iIndepFun_Y := iIndepFun_infinitePi (X := fun _ => (id : ℝ → ℝ)) fun _ => measurable_id
  real_Y_le i t := by
    rw [cdf_eq_real, ← Measure.infinitePi_map_eval (fun _ => expMeasure 1) i,
      map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic]
    rfl
  count_lln ε hε := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hset : {ω : ℕ → ℝ | ε ≤ |(n : ℝ) / n - (1 : ℝ)⁻¹|} = ∅ := by
      ext ω; simp [div_self hn', not_le.2 hε]
    rw [hset, measureReal_empty]
  le_of_forall_le := ae_of_all _ fun ω n t h =>
    Finset.sup'_le _ _ fun i hi => h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  le_of_lt_count := ae_of_all _ fun ω n i hi =>
    Finset.le_sup' ω (Finset.mem_range.2 (by omega))

theorem expLadder_tail :
    Tendsto (fun t => (1 - expLadder.F t) * Real.exp (1 * t)) atTop (𝓝 1) :=
  tendsto_tail_of_eq_exp fun t ht => by
    change 1 - cdf (expMeasure 1) t = _
    rw [cdf_expMeasure_eq one_pos]; simp [ht]

end Cslib.Bioinformatics.Alignment.ScoreSignificance
