/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.IntegrationSubcriticalAssembly
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.IntegrationSubcriticalAssembly`

* `Sig` and `isc_Sig_succ` on a step model.
* `isc_subcritical_decay` (the headline) for the step model `θ_0 = 1`, `θ_k = 0` (`k ≥ 1`):
  `Σ_n = 1` for `n ≥ 1`, the differential inequality `hdiff` and the polynomial bound `hSpoly`
  (`1 ≤ n^{1/2}`) hold, and the conclusion follows.
-/

@[expose] public section

open StatMech.OSSS.IntegrationSubcritical

namespace MathlibExtTest.StatMech.Probability.OSSS.IntegrationSubcriticalAssembly

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

example (x : ℝ) : Sig θ 2 x = Sig θ 1 x + θ 1 x := isc_Sig_succ θ 1 x

example : ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
    θ n (3 - 2 * 1) ≤ 1 * Real.exp (-(((n : ℝ) / Q) * 1)) :=
  isc_subcritical_decay θ (fun _ _ => 0) (1 / 2) 1 3 1 1 one_pos (by norm_num) (by norm_num)
    zero_le_one le_rfl (fun _ _ _ => by unfold θ; exact hasDerivAt_const _ _)
    (fun _ _ _ => by unfold θ; split <;> norm_num) (fun _ _ _ => by unfold θ; split <;> norm_num)
    (fun _ _ _ _ _ _ => le_rfl) (fun n hn x _ => by rw [Sig_θ hn]; exact one_pos)
    (fun n hn x _ => by rw [θ_succ n hn]; simp)
    (fun n hn => by
      rw [Sig_θ hn]
      exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

end MathlibExtTest.StatMech.Probability.OSSS.IntegrationSubcriticalAssembly
