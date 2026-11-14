/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.Calibration
public import CSLibExtTest.Bioinformatics.Alignment.ScoreSignificance.ExpFixture

/-!
# Karlin–Altschul p-value calibration tests

* Values of `gumbelPValue` and `gumbelLevel`: positivity, the bound `≤ 1`, the rejection region
  and `exp (-K e^{-θ x_α}) = 1 - α` at `α = 1 / 2`.
* The Gumbel distribution function and level as the shared `gumbelCDF` and `gumbelQuantile` at
  concrete parameters, and `exp (-K e^{-θ x_α}) = 1 - α` recovered from the shared inverse lemma.
* A nontrivial instance of the generic calibration theorems `tendsto_real_gumbelPValue_le` and
  `eventually_real_gumbelPValue_le_le`: `Mₙ` the maximum of `n + 1` i.i.d. `Exp(1)` variables
  (a `LadderInput` with one excursion per step, `θ = K = 1`). The p-value
  `1 - exp (-n e^{-Mₙ})` satisfies `P(pₙ ≤ α) → α` for every `α ∈ [0, 1]`.
* The null-model theorems applied to arbitrary nonlattice and lattice renewal inputs. These are
  restatements only: no `NonlatticeRenewalInput` or `LatticeRenewalInput` instance exists yet
  (see `GumbelTail`), so they are not exercised on a concrete model.
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

/-! ### The Gumbel level through the shared Gumbel API -/

/-- With `K = e` and `θ = 1`, the distribution function `exp (-K e^{-θ x})` is the shared
`gumbelCDF` with location `1` and scale `1`. -/
example (x : ℝ) : Real.exp (-(Real.exp 1 * Real.exp (-(1 * x)))) = gumbelCDF 1 1 x := by
  simpa using exp_neg_mul_exp_eq_gumbelCDF (Real.exp_pos 1) one_pos x

/-- With `K = e` and `θ = 1`, the Gumbel level at `α = 1 - e⁻¹` is the shared quantile at `e⁻¹`,
which is the location `1`. -/
example : gumbelLevel (Real.exp 1) 1 (1 - Real.exp (-1)) = 1 := by
  rw [gumbelLevel_eq_gumbelQuantile (Real.exp_pos 1)
    (sub_pos.2 (Real.exp_lt_one_iff.2 (by norm_num))) (sub_lt_self 1 (Real.exp_pos (-1)))]
  simp [gumbelQuantile]

/-- `exp_neg_mul_exp_gumbelLevel` at `K = 2`, `θ = 3`, `α = 1 / 20`, obtained from the shared
inverse lemma `gumbelCDF_gumbelQuantile` through the two bridges. -/
example : Real.exp (-(2 * Real.exp (-(3 * gumbelLevel 2 3 (1 / 20))))) = 1 - 1 / 20 := by
  rw [exp_neg_mul_exp_eq_gumbelCDF two_pos three_pos,
    gumbelLevel_eq_gumbelQuantile two_pos (by norm_num) (by norm_num)]
  exact gumbelCDF_gumbelQuantile (by norm_num) (by norm_num) (by norm_num)

/-! ### A nontrivial instance: maxima of i.i.d. exponential variables -/

theorem measurable_runMax (n : ℕ) : Measurable (runMax n) :=
  Finset.measurable_range_sup'' fun k _ => measurable_pi_apply k

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
