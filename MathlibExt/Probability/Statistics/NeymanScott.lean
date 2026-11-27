/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Neyman–Scott log-likelihood for equal pairs

When all pairs agree, the joint Gaussian log-likelihood is unbounded above as the common
variance decreases to zero.
-/

@[expose] public section

namespace WantedExt.Probability.Statistics.NeymanScottWanted

/-- **Gaussian log-likelihood of the pairs.** The Gaussian log-likelihood of `n` pairs
`y i 0, y i 1` with pair means `α i` and variance `s > 0`:
`∑_i ∑_t (-(1/2) log (2 π s) - (y_{it} - α_i)² / (2 s))`. -/
noncomputable def logLik {n : ℕ} (y : Fin n → Fin 2 → ℝ) (α : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i, ∑ t, (-(1 / 2) * Real.log (2 * Real.pi * s) - (y i t - α i) ^ 2 / (2 * s))

/-- **No maximum when all pairs agree.** For `n ≥ 1` real pairs with
`y i 0 = y i 1` for every `i`, the log-likelihood at `α_i = y i 0` is unbounded above over `s > 0`:
for every `M` there is `s > 0` with log-likelihood greater than `M`.

Sources: J. Neyman and E. L. Scott, "Consistent estimates based on partially consistent
observations", Econometrica 16 (1948) 1–32; derived. -/
theorem logLik_unbounded {n : ℕ} (hn : 0 < n) (y : Fin n → Fin 2 → ℝ)
    (heq : ∀ i, y i 0 = y i 1) (M : ℝ) :
    ∃ s : ℝ, 0 < s ∧ M < logLik y (fun i => y i 0) s := by
  have hlogLik (s : ℝ) : logLik y (fun i => y i 0) s = -(n : ℝ) * Real.log (2 * Real.pi * s) := by
    calc
      logLik y (fun i => y i 0) s = ∑ _i : Fin n, -Real.log (2 * Real.pi * s) := by
        unfold logLik
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.sum_univ_two, heq i, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
          zero_div, sub_zero]
        ring
      _ = -(n : ℝ) * Real.log (2 * Real.pi * s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg, neg_mul]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hπ : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  let x : ℝ := -(M + 1) / (n : ℝ)
  let s : ℝ := Real.exp x / (2 * Real.pi)
  have hslog : Real.log (2 * Real.pi * s) = x := by
    dsimp [s]
    rw [mul_div_cancel₀ _ hπ.ne', Real.log_exp]
  have hvalue : logLik y (fun i => y i 0) s = M + 1 := by
    rw [hlogLik, hslog]
    dsimp [x]
    rw [← mul_div_assoc, neg_mul_neg, mul_div_cancel_left₀ _ hn'.ne']
  exact ⟨s, div_pos (Real.exp_pos _) hπ, hvalue ▸ lt_add_of_pos_right M zero_lt_one⟩

end WantedExt.Probability.Statistics.NeymanScottWanted
