/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.Calibration
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Karlin–Altschul p-value calibration tests

* Values of `gumbelPValue` and `gumbelLevel`: positivity, the bound `≤ 1`, the rejection region
  and `exp (-K e^{-θ x_α}) = 1 - α` at `α = 1 / 2`.
* A nontrivial instance of the calibration theorem: `Mₙ` the maximum of `n + 1` i.i.d. `Exp(1)`
  variables (a `LadderInput` with one excursion per step, `θ = K = 1`). The p-value
  `1 - exp (-n e^{-Mₙ})` satisfies `P(pₙ ≤ α) → α` for every `α ∈ [0, 1]`.
* The null-model theorems applied to arbitrary nonlattice and lattice renewal inputs.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### The p-value and the Gumbel level -/

example : gumbelPValue 1 1 1 0 = 1 - Real.exp (-1) := by simp [gumbelPValue]

example : gumbelPValue 2 1 0 5 = 0 := by simp [gumbelPValue]

example (s : ℝ) : 0 < gumbelPValue 2 3 10 s := gumbelPValue_pos (by norm_num) (by norm_num) s

example (s : ℝ) : gumbelPValue 2 3 10 s ≤ 1 := gumbelPValue_le_one s

/-- At level `1 / 2`, with `K = θ = 1` and `n = 4`, the rejection region is
`s ≥ log 4 + log (1 / log 2)`. -/
example (s : ℝ) :
    gumbelPValue 1 1 4 s ≤ 1 / 2 ↔ Real.log 4 + Real.log (1 / Real.log 2) ≤ s := by
  rw [gumbelPValue_le_iff one_pos one_pos (by norm_num) (by norm_num) (by norm_num)]
  have h : -Real.log (1 - 1 / 2 : ℝ) = Real.log 2 := by
    rw [show (1 - 1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  simp only [gumbelLevel, h, div_one, Nat.cast_ofNat]

example : Real.exp (-(1 * Real.exp (-(1 * gumbelLevel 1 1 (1 / 2))))) = 1 / 2 := by
  rw [exp_neg_mul_exp_gumbelLevel one_pos one_pos (by norm_num) (by norm_num)]; norm_num

/-! ### A nontrivial instance: maxima of i.i.d. exponential variables -/

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- I.i.d. `Exp(1)` coordinates. -/
noncomputable abbrev Pexp : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => expMeasure 1

/-- The running maximum `max_{i ≤ n} ω i`. -/
noncomputable def runMax (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ ω

theorem measurable_runMax (n : ℕ) : Measurable (runMax n) :=
  Finset.measurable_range_sup'' fun k _ => measurable_pi_apply k

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

/-- The classical Gumbel limit for this model, in the form the calibration theorems take:
`P(Mₙ ≤ log n / 1 + x) → exp (-(1 · e^{-1 · x}))`. -/
theorem runMax_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => Pexp.real {ω | runMax n ω ≤ Real.log n / 1 + x}) atTop
      (𝓝 (Real.exp (-(1 * Real.exp (-(1 * x)))))) := by
  simpa [expLadder] using expLadder.tendsto_real_le_log_div_add one_pos expLadder_tail x

/-- **Exact calibration on a concrete model.** For the maximum `Mₙ` of `n + 1` i.i.d. `Exp(1)`
variables, the p-value `1 - exp (-n e^{-Mₙ})` satisfies `P(pₙ ≤ α) → α`. -/
example {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => Pexp.real {ω | gumbelPValue 1 1 n (runMax n ω) ≤ α}) atTop (𝓝 α) :=
  tendsto_real_gumbelPValue_le measurable_runMax one_pos one_pos runMax_tendsto hα

/-- The same model at level `α = 1 / 20`: eventually `P(pₙ ≤ 0.05) ≤ 0.05 + 0.01`. -/
example : ∀ᶠ n : ℕ in atTop,
    Pexp.real {ω | gumbelPValue 1 1 n (runMax n ω) ≤ 1 / 20} ≤ 1 / 20 + 1 / 100 :=
  eventually_real_gumbelPValue_le_le measurable_runMax one_pos one_pos
    (fun x ε hε => ((runMax_tendsto x).eventually (lt_mem_nhds (sub_lt_self _ hε))).mono
      fun _ h => h.le)
    ⟨by norm_num, by norm_num⟩ (by norm_num)

/-! ### The null-model theorems -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

example (R : NonlatticeRenewalInput P X) (hC : 0 < R.C) :
    Tendsto (fun n : ℕ =>
        P.real {ω | gumbelPValue R.K R.θ n (maxSegmentScoreRV X n ω) ≤ 1 / 20}) atTop
      (𝓝 (1 / 20)) :=
  R.tendsto_real_gumbelPValue_le hC ⟨by norm_num, by norm_num⟩

example (R : NonlatticeRenewalInput P X) (hC : 0 < R.C) {α ε : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      P.real {ω | gumbelPValue R.K R.θ n (maxSegmentScoreRV X n ω) ≤ α} ≤ α + ε :=
  R.eventually_real_gumbelPValue_le_le hC hα hε

example (R : LatticeRenewalInput P X) (hC : 0 < R.C) {α ε : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      P.real {ω | gumbelPValue R.K R.θ n (maxSegmentScoreRV X n ω) ≤ α} ≤ α + ε :=
  R.eventually_real_gumbelPValue_le_le hC hα hε

example (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (maxSegmentScoreRV X n) :=
  measurable_maxSegmentScoreRV hX n

end Cslib.Bioinformatics.Alignment.ScoreSignificance
