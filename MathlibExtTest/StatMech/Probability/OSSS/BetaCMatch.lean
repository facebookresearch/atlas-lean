/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.BetaCMatch
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.BetaCMatch`

* `bcm_theta_zero_of_decay`, `bcm_expBound_tendsto_zero`.
* `bcm_betaC_eq_threshold` for `Θ β = max 0 β`: `sup {Θ = 0} = 0`.
* `bcm_betaC_eq_beta1` for the step model `θ_0 = 1`, `θ_k = 0` (whose `beta1` is `0`) and
  `Θ β = max 0 β`, with `hdecay` and `hmf` discharged.
-/

@[expose] public section

open StatMech.OSSS.IntegrationSubcritical StatMech.OSSS.BetaThresholdBound StatMech.OSSS.BetaCMatch

namespace MathlibExtTest.StatMech.Probability.OSSS.BetaCMatch

/-- A step model: `θ_0 = 1` and `θ_k = 0` for `k ≥ 1` (constant in `x`), so `Σ_n = 1` for
`n ≥ 1`. -/
noncomputable def θ (k : ℕ) (_ : ℝ) : ℝ := if k = 0 then 1 else 0

theorem Sig_θ {n : ℕ} (hn : 1 ≤ n) (x : ℝ) : Sig θ n x = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  unfold Sig
  rw [Finset.sum_range_succ']
  simp [θ]

theorem θ_succ (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : θ n x = 0 := by
  simp [θ]; omega

/-- `log Σ_n / log n = 0` for the step model (for `n ≥ 1`, `Σ_n = 1`; for `n = 0`, `log 0 = 0`). -/
theorem logRatio_θ (b : ℝ) : logRatio (fun n => Sig θ n b) = fun _ => 0 := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logRatio]
  · simp [logRatio, Sig_θ hn]

theorem thresholdSet_θ : thresholdSet (fun b n => Sig θ n b) = ∅ := by
  ext b
  simp only [thresholdSet, logRatio_θ, Filter.limsup_const, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false, not_le]
  norm_num

theorem beta1_θ : beta1 (fun b n => Sig θ n b) = 0 := by
  rw [beta1, thresholdSet_θ, Real.sInf_empty]

example : (0 : ℝ) = 0 :=
  bcm_theta_zero_of_decay 0 1 1 1 one_pos one_pos le_rfl (fun _ => by positivity)

example : Filter.Tendsto (fun n : ℕ => 1 * Real.exp (-(((n : ℝ) / 1) * 1))) Filter.atTop
    (nhds 0) := bcm_expBound_tendsto_zero 1 1 1 one_pos one_pos

example : sSup (bcm_subcriticalSet (fun b : ℝ => max 0 b)) = 0 :=
  bcm_betaC_eq_threshold _ 0 (fun _ hβ => max_eq_left hβ.le) (fun _ hβ => lt_max_of_lt_right hβ)

example : sSup (bcm_subcriticalSet (fun b : ℝ => max 0 b)) = beta1 (fun b n => Sig θ n b) :=
  bcm_betaC_eq_beta1 θ (fun β => max 0 β) 1 (fun _ => 1) (fun _ => 1)
    (fun β hβ => by
      rw [beta1_θ] at hβ
      refine ⟨le_max_left _ _, one_pos, one_pos, fun n => ?_⟩
      rw [max_eq_left hβ.le]; positivity)
    (fun β hβ => by rw [beta1_θ] at hβ ⊢; simp)

end MathlibExtTest.StatMech.Probability.OSSS.BetaCMatch
