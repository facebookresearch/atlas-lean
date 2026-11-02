/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.FKSharpDiffIneq
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.FKSharpDiffIneq`

* `fkd_diff_ineq_pointwise` and `fkd_engine_rate_of_assembled` at small numeric inputs.
* `fkd_diff_ineq_pointwise_weighted` on a one-edge set.
* The headline `fk_q2_subcritical_decay_of_cov` for a step model on one edge (`θ_0 = 1/2`,
  `θ_k = 0` for `k ≥ 1`, zero covariance, `J = 1`, `β = 3`, `δ = 1`), with every hypothesis
  discharged; `Sgn` is the function forced by `hident`.
-/

@[expose] public section

open StatMech.OSSS.FKSharpDiffIneq StatMech.OSSS.IntegrationSubcritical

namespace MathlibExtTest.StatMech.Probability.OSSS.FKSharpDiffIneq

example : (1 * (2 : ℕ) / (4 * 1)) * ((1 / 2 : ℝ) * (1 - 1 / 2)) ≤ 1 :=
  fkd_diff_ineq_pointwise 2 1 1 (1 / 2) 1 (1 / 4) one_pos zero_le_one (by norm_num) (by norm_num)

example : ((2 : ℕ) / 2 : ℝ) * (1 / 2) ≤ 1 :=
  fkd_engine_rate_of_assembled 2 1 (1 / 4) (1 / 2) 1 2 (by norm_num) one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : ∃ cR : ℝ, 0 < cR ∧ (cR * ((0 : ℕ) : ℝ) / (4 * 1)) * ((1 / 2 : ℝ) * (1 - 1 / 2)) ≤ 0 :=
  fkd_diff_ineq_pointwise_weighted (E := Unit) 0 1 (1 / 2) 0 (fun _ => 1) (fun _ => 0) 1 one_pos
    (fun _ => one_pos) one_pos (fun _ => le_rfl) (by simp) (by simp)

/-- Step model with values in `[0, 1)`: `θ_0 = 1/2`, `θ_k = 0` for `k ≥ 1`. -/
noncomputable def θ (k : ℕ) (_ : ℝ) : ℝ := if k = 0 then 1 / 2 else 0

theorem Sig_θ {n : ℕ} (hn : 1 ≤ n) (x : ℝ) : Sig θ n x = 1 / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  unfold Sig
  rw [Finset.sum_range_succ']
  simp [θ]

theorem θ_succ (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : θ n x = 0 := by
  simp [θ]; omega

/-- The Russo prefactor for `J = 1`. -/
noncomputable def cR (_ : ℕ) (x : ℝ) : ℝ := 1 / (Real.exp (x * 1) - 1)

/-- The function `Sgn` forced by `hident` (and `1` at `n = 0`). -/
noncomputable def Sgn (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then 1 else Sig θ n x * (cR n x * (1 - θ n x)) / 4

theorem cR_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < cR n x :=
  div_pos one_pos (by have := Real.one_lt_exp_iff.mpr (by linarith : 0 < x * 1); linarith)

example : ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
    θ n (3 - 2 * 1) ≤ 1 * Real.exp (-(((n : ℝ) / Q) * 1)) := by
  have hx : ∀ x ∈ Set.Icc (3 - 2 * 1 : ℝ) 3, 0 < x := fun x hx => by linarith [hx.1]
  refine fk_q2_subcritical_decay_of_cov (E := Unit) θ (fun _ _ => 0) (fun _ => 1)
    (fun _ _ _ => 0) Sgn cR (1 / 2) 1 3 1 1 one_pos (by norm_num) (by norm_num) zero_le_one le_rfl
    (fun _ => one_pos) hx (fun _ _ _ => by unfold θ; exact hasDerivAt_const _ _)
    (fun _ _ _ => by unfold θ; split <;> norm_num) (fun _ _ _ => by unfold θ; split <;> norm_num)
    (fun _ _ _ => by unfold θ; split <;> norm_num) (fun _ _ _ _ _ _ => le_rfl)
    (fun n hn x _ => by rw [Sig_θ hn]; norm_num) ?_ (fun _ _ _ _ => le_rfl) (fun _ _ _ => by simp)
    ?_ (fun n x hx' => ⟨cR_pos (hx x hx') n, fun _ => le_rfl⟩) ?_ ?_
  · intro n x hx'
    unfold Sgn
    split_ifs with h
    · exact one_pos
    · rw [Sig_θ (Nat.one_le_iff_ne_zero.mpr h), θ_succ n (Nat.one_le_iff_ne_zero.mpr h)]
      have := cR_pos (hx x hx') n
      positivity
  · intro n x _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [θ_succ n hn]; simp
  · intro n hn x _
    simp only [Sgn, Nat.one_le_iff_ne_zero.mp hn, ite_false]
    ring
  · intro n hn
    rw [Sig_θ hn]
    exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

end MathlibExtTest.StatMech.Probability.OSSS.FKSharpDiffIneq
