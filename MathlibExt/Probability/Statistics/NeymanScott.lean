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

/-- **Maximum-likelihood variance estimate.** The estimate
`σ̂² = (1 / (4n)) ∑_i (y_{i1} - y_{i2})²`. -/
noncomputable def mleVariance {n : ℕ} (y : Fin n → Fin 2 → ℝ) : ℝ :=
  (∑ i, (y i 0 - y i 1) ^ 2) / (4 * n)

/-- **The joint maximum-likelihood estimate.** For real pairs
`y i 0, y i 1`, `i < n`, with `∑_i (y_{i1} - y_{i2})² > 0`, the log-likelihood over pair means
`α ∈ ℝⁿ` and variance `s > 0` is maximized exactly at `α̂_i = (y_{i1} + y_{i2}) / 2` and
`s = σ̂² = (1 / (4n)) ∑_i (y_{i1} - y_{i2})²`: for every `α` and every `s > 0` the log-likelihood
is at most its value there, with equality only when `α = α̂` and `s = σ̂²`.

Sources: J. Neyman and E. L. Scott, "Consistent estimates based on partially consistent
observations", Econometrica 16 (1948) 1–32; the characterization is derived. -/
theorem logLik_max {n : ℕ} (y : Fin n → Fin 2 → ℝ)
    (hd : 0 < ∑ i, (y i 0 - y i 1) ^ 2) (α : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    logLik y α s ≤ logLik y (fun i => (y i 0 + y i 1) / 2) (mleVariance y) ∧
      (logLik y α s = logLik y (fun i => (y i 0 + y i 1) / 2) (mleVariance y) ↔
        α = (fun i => (y i 0 + y i 1) / 2) ∧ s = mleVariance y) := by
  let m : Fin n → ℝ := fun i => (y i 0 + y i 1) / 2
  let v := mleVariance y
  let t := v / s
  have hn : 0 < n := by
    by_contra! hn
    have h : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simp at hd
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < 4 * (n : ℝ) := mul_pos (by norm_num) hn'
  have hv : 0 < v := div_pos hd hden
  have ht : 0 < t := div_pos hv hs
  have hsum : (∑ i, (y i 0 - y i 1) ^ 2) = 4 * (n : ℝ) * v := by
    calc
      _ = v * (4 * (n : ℝ)) := ((eq_div_iff hden.ne').mp (show v = _ from rfl)).symm
      _ = _ := mul_comm _ _
  -- Complete the square in each pair mean before summing over the pairs.
  have hprofile (a : Fin n → ℝ) (u : ℝ) (hu : 0 < u) :
      logLik y a u = -(n : ℝ) * Real.log (2 * Real.pi * u) - (n : ℝ) * (v / u) -
        (∑ i, (a i - m i) ^ 2) / u := by
    calc
      logLik y a u = ∑ i, (-Real.log (2 * Real.pi * u) - (y i 0 - y i 1) ^ 2 / (4 * u) -
          (a i - m i) ^ 2 / u) := by
        unfold logLik
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_two]
        dsimp [m]
        field_simp [hu.ne']
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_neg, hsum]
        field_simp [hu.ne']
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hlog : Real.log (2 * Real.pi * v) - Real.log (2 * Real.pi * s) = Real.log t := by
    rw [← Real.log_div (mul_ne_zero hπ hv.ne') (mul_ne_zero hπ hs.ne')]
    congr 1
    dsimp [t]
    field_simp [hπ, hs.ne']
  have hgap : logLik y m v - logLik y α s =
      (n : ℝ) * (t - 1 - Real.log t) + (∑ i, (α i - m i) ^ 2) / s := by
    rw [hprofile m v hv, hprofile α s hs]
    simp only [div_self hv.ne', mul_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, zero_div, sub_zero]
    calc
      _ = (n : ℝ) * (t - 1 - (Real.log (2 * Real.pi * v) - Real.log (2 * Real.pi * s))) +
          (∑ i, (α i - m i) ^ 2) / s := by
        dsimp [t]
        ring
      _ = _ := by rw [hlog]
  have hterm : 0 ≤ (n : ℝ) * (t - 1 - Real.log t) :=
    mul_nonneg hn'.le (sub_nonneg.mpr (Real.log_le_sub_one_of_pos ht))
  have hres : 0 ≤ (∑ i, (α i - m i) ^ 2) / s :=
    div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (α i - m i)) hs.le
  change logLik y α s ≤ logLik y m v ∧ (logLik y α s = logLik y m v ↔ α = m ∧ s = v)
  refine ⟨sub_nonneg.mp (by rw [hgap]; exact add_nonneg hterm hres), ?_⟩
  constructor
  · intro heq
    have hzero : (n : ℝ) * (t - 1 - Real.log t) + (∑ i, (α i - m i) ^ 2) / s = 0 := by
      rw [← hgap, heq, sub_self]
    have ht1 : t = 1 := by
      by_contra hne
      have hpos := mul_pos hn' (sub_pos.mpr (Real.log_lt_sub_one_of_pos ht hne))
      linarith
    have hsv : s = v := by
      have h := (div_eq_iff hs.ne').mp ht1
      simpa using h.symm
    have hres_zero : (∑ i, (α i - m i) ^ 2) / s = 0 := by linarith
    have hsquares : (∑ i, (α i - m i) ^ 2) = 0 := by
      simpa using (div_eq_iff hs.ne').mp hres_zero
    refine ⟨funext fun i => ?_, hsv⟩
    have hi : (α i - m i) ^ 2 ≤ ∑ j, (α j - m j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (α j - m j)) (Finset.mem_univ i)
    rw [hsquares] at hi
    have hi_zero : (α i - m i) ^ 2 = 0 := le_antisymm hi (sq_nonneg _)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp (by simpa only [pow_two] using hi_zero))
  · rintro ⟨rfl, rfl⟩
    rfl

end WantedExt.Probability.Statistics.NeymanScottWanted
