/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.BetaThresholdBound
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.BetaThresholdBound`

* `btb_poly_bound_of_ratio_lt` at `n = 4`, `S = 1`; `btb_Sig_le_card`.
* For the step model `θ_0 = 1`, `θ_k = 0` (`k ≥ 1`): `logRatio` vanishes, `thresholdSet = ∅`
  and `beta1 = 0`; the headline `btb_fk_q2_subcritical_decay_of_threshold'` applies at `β = -1`.
-/

@[expose] public section

open StatMech.OSSS.IntegrationSubcritical StatMech.OSSS.BetaThresholdBound

namespace MathlibExtTest.StatMech.Probability.OSSS.BetaThresholdBound

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

example : (1 : ℝ) < (4 : ℕ) ^ (1 - (1 / 2 : ℝ)) :=
  btb_poly_bound_of_ratio_lt 4 1 (1 / 2) (by norm_num) one_pos (by norm_num)

example (n : ℕ) : Sig θ n 0 ≤ n :=
  btb_Sig_le_card θ 0 (fun k => by unfold θ; split <;> norm_num) n

example : ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
    θ n (-1 - 2 * 1) ≤ 1 * Real.exp (-(((n : ℝ) / Q) * 1)) :=
  btb_fk_q2_subcritical_decay_of_threshold' θ (fun _ _ => 0) 1 (-1) 1 one_pos zero_le_one
    (fun _ _ _ => by unfold θ; exact hasDerivAt_const _ _)
    (fun _ _ _ => by unfold θ; split <;> norm_num) (fun _ _ _ => by unfold θ; split <;> norm_num)
    (fun _ _ _ _ _ _ => le_rfl) (fun n hn x _ => by rw [Sig_θ hn]; exact one_pos)
    (fun n hn x _ => by rw [θ_succ n hn]; simp)
    (fun n hn => by rw [Sig_θ (by omega)]; exact one_pos)
    (fun k => by unfold θ; split <;> norm_num) (by rw [thresholdSet_θ]; exact bddBelow_empty)
    (by rw [beta1_θ]; norm_num)

end MathlibExtTest.StatMech.Probability.OSSS.BetaThresholdBound
