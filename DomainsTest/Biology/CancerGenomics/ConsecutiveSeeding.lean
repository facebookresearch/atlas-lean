/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.CancerGenomics.ConsecutiveSeeding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

/-! Tests for negative binomial clone sizes under consecutive seeding: the success probability
and the mean at concrete parameters, the empty site at time `0`, and a family of three clones
for which the hypotheses of the main theorem hold (non-vacuity). -/

namespace MathlibExtTest.Biology.CancerGenomics.ConsecutiveSeeding

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open MathlibExt.Biology.CancerGenomics.ConsecutiveSeeding

/-- At time `0` the success probability is `1`: the site is empty. -/
example : successProb 2 1 0 = 1 := by
  norm_num [successProb]

/-- With `b = 2`, `d = 1` (`ρ = 1/2`, `r = 1`) and `e^{r t} = 2`, `q = (1/2) / (1/2 + 1) = 1/3`. -/
example : successProb 2 1 (log 2) = 1 / 3 := by
  simp only [successProb]
  rw [show ((2 : ℝ) - 1) * log 2 = log 2 by ring, exp_log (by norm_num)]
  norm_num

/-- With `lam = 2`, `b = 2`, `d = 1` (`k = 1`, `ρ = 1/2`) and `e^{r t} = 2`, `ȳ = 2`. -/
example : meanSize 2 2 1 (log 2) = 2 := by
  simp only [meanSize]
  rw [show ((2 : ℝ) - 1) * log 2 = log 2 by ring, exp_log (by norm_num)]
  norm_num

/-- `q = k / (ȳ + k)` at these parameters: `1/3 = 1 / (2 + 1)`. -/
example : successProb 2 1 (log 2) = 2 / 2 / (meanSize 2 2 1 (log 2) + 2 / 2) :=
  successProb_eq_div (by norm_num) (by norm_num) (by norm_num) (log_nonneg (by norm_num))

example (lam b d : ℝ) : meanSize lam b d 0 = 0 := meanSize_zero lam b d

/-- The negative binomial law at time `0` is the point mass at `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ≥0} {b d : ℝ}
    {T : ℕ → Ω → ℝ} {X : ℝ≥0 → ℕ → Ω → ℕ} (h : IsClonalSeeding P lam b d T X)
    (hlam : 0 < lam) (hd : 0 ≤ d) (hdb : d < b) :
    P.real {ω | cloneSize T X 0 ω = 0} = 1 := by
  have hb : 0 < b := by linarith
  have hq : successProb b d 0 = 1 := by
    have hρ : 1 - d / b ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hb.ne']
      exact hdb.ne
    simp [successProb, hρ]
  rw [h.measureReal_cloneSize hlam hd hdb 0 0, NNReal.coe_zero, hq]
  simp [negBinomialPMF]

/-- Three clones with seeding rates `1, 2, 3`, `b = 2`, `d = 1`: the model exists, so the main
theorem applies; at time `0` every clone is empty with probability one. -/
example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (T : Fin 3 → ℕ → Ω → ℝ)
    (X : Fin 3 → ℝ≥0 → ℕ → Ω → ℕ), ∀ i,
      P.real {ω | cloneSize (T i) (X i) 0 ω = 0} =
        negBinomialPMF ((i + 1 : ℕ) / 2) (successProb 2 1 0) 0 := by
  obtain ⟨Ω, _, P, T, X, _, h, hind⟩ := exists_isClonalSeeding (fun i : Fin 3 ↦ ((i + 1 : ℕ) : ℝ≥0))
    (fun i ↦ by positivity) (b := 2) (d := 1) (by norm_num) (by norm_num)
  refine ⟨Ω, inferInstance, P, T, X, fun i ↦ ?_⟩
  have := ((negBinomial_cloneSizes (by norm_num) (by norm_num) (fun i ↦ by positivity) h
    hind).2 0).2.1 i 0
  simpa using this

end MathlibExtTest.Biology.CancerGenomics.ConsecutiveSeeding
