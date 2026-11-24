/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.SmallSetExpansion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Level-k Inequalities

Small subsets of the cube have little Fourier weight at low degrees. For `f : {-1, 1}ⁿ → {0, 1}`
of mean `α`, the Small-Set Expansion Theorem `Stab_ρ[f] ≤ α^{2/(1+ρ)}` and
`Stab_ρ[f] ≥ ρ^k W^{≤k}[f]` give `W^{≤k}[f] ≤ ρ^{-k} α^{2(1-ρ)}`; the choice
`ρ = k / (2 ln(1/α))` yields O'Donnell's Level-k Inequalities
`W^{≤k}[f] ≤ (2e/k · ln(1/α))^k α²` for `k ≤ 2 ln(1/α)`. The case `k = 1` is the Level-1
Inequality `W¹[f] ≤ O(α² log(1/α))` for `α ≤ 1/2`.

## Main statements

* `BooleanCube.level_k_inequality`: the Level-k Inequalities.
* `BooleanCube.level_one_inequality`: the Level-1 Inequality, with constant `2e`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Level-k Inequalities (Section 9.5) and Level-1 Inequality (Section 5.4).
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

variable {n : ℕ}

/-- **Level-k Inequalities.** Let `f : BoolCube n → ℝ` take values in `{0, 1}`, with mean
`α = 𝔼[f]`, and let `k ≥ 1` be a natural number with `k ≤ 2 ln(1/α)`. Then
`W^{≤k}[f] = ∑_{|S| ≤ k} f̂(S)² ≤ (2e/k · ln(1/α))^k α²` (R. O'Donnell, *Analysis of Boolean
Functions*, 2014, Level-k Inequalities, Section 9.5). -/
theorem level_k_inequality {f : BoolCube n → ℝ} (hf : ∀ x, f x = 0 ∨ f x = 1) {k : ℕ}
    (hk : 1 ≤ k) (hkα : (k : ℝ) ≤ 2 * Real.log (1 / 𝔼 x, f x)) :
    ∑ S with S.card ≤ k, boolFourierCoeff n f S ^ 2 ≤
      (2 * Real.exp 1 / k * Real.log (1 / 𝔼 x, f x)) ^ k * (𝔼 x, f x) ^ 2 := by
  set α := 𝔼 x, f x with hα
  set L := Real.log (1 / α) with hL
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hLpos : 0 < L := by linarith
  have hα0 : 0 ≤ α := Finset.expect_nonneg fun x _ => by rcases hf x with h | h <;> simp [h]
  have hαpos : 0 < α := by
    rcases hα0.eq_or_lt with h | h
    · rw [← h] at hL
      simp [hL] at hLpos
    · exact h
  have hlogα : Real.log α = -L := by rw [hL, one_div, Real.log_inv, neg_neg]
  set ρ := (k : ℝ) / (2 * L) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one (by positivity)]; exact hkα
  -- `ρ^k W^{≤k}[f] ≤ Stab_ρ[f]`.
  have hlow : ρ ^ k * ∑ S with S.card ≤ k, boolFourierCoeff n f S ^ 2 ≤ boolNoiseStab ρ f := by
    rw [boolNoiseStab_eq_sum, Finset.mul_sum]
    calc ∑ S with S.card ≤ k, ρ ^ k * boolFourierCoeff n f S ^ 2
        ≤ ∑ S with S.card ≤ k, ρ ^ S.card * boolFourierCoeff n f S ^ 2 :=
          Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hρ0.le hρ1 (Finset.mem_filter.mp hS).2) (sq_nonneg _)
      _ ≤ ∑ S, ρ ^ S.card * boolFourierCoeff n f S ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun S _ _ => by positivity
  -- Small-set expansion and `α^{2/(1+ρ)} ≤ α^{2(1-ρ)} = e^k α²`.
  have hsse := boolNoiseStab_le_rpow_of_indicator hρ0.le hρ1 hf
  have hexp : α ^ (2 / (1 + ρ)) ≤ Real.exp k * α ^ 2 := by
    have hα1 : α ≤ 1 := by
      have : (0 : ℝ) < Real.log (1 / α) := hLpos
      rw [Real.log_pos_iff (by positivity)] at this
      rw [lt_one_div (by norm_num) hαpos] at this
      linarith [this]
    calc α ^ (2 / (1 + ρ)) ≤ α ^ (2 * (1 - ρ)) := by
          refine Real.rpow_le_rpow_of_exponent_ge hαpos hα1 ?_
          rw [le_div_iff₀ (by linarith)]
          nlinarith
      _ = Real.exp k * α ^ 2 := by
          rw [Real.rpow_def_of_pos hαpos, hlogα, ← Real.rpow_natCast,
            Real.rpow_def_of_pos hαpos, hlogα, ← Real.exp_add]
          congr 1
          rw [hρ]
          field_simp
          push_cast
          ring
  have hmain : ρ ^ k * ∑ S with S.card ≤ k, boolFourierCoeff n f S ^ 2 ≤
      Real.exp k * α ^ 2 := (hlow.trans hsse).trans hexp
  have hρk : 0 < ρ ^ k := pow_pos hρ0 k
  rw [← le_div_iff₀' hρk] at hmain
  refine hmain.trans_eq ?_
  rw [hρ, div_pow, mul_pow, mul_pow, div_pow, mul_pow, Real.exp_one_pow]
  field_simp

/-- **Level-1 Inequality.** There is a universal constant `C` such that every
`f : BoolCube n → ℝ` with values in `{0, 1}` and mean `α = 𝔼[f] ≤ 1/2` satisfies
`W¹[f] ≤ C α² log(1/α)` (R. O'Donnell, *Analysis of Boolean Functions*, 2014, Level-1
Inequality, Section 5.4, stated there as `W¹[f] ≤ O(α² log(1/α))`; proved in Section 5.4 and,
via hypercontractivity, in Section 9.5). For `α = 0` both sides vanish. -/
theorem level_one_inequality :
    ∃ C : ℝ, ∀ (n : ℕ) (f : BoolCube n → ℝ), (∀ x, f x = 0 ∨ f x = 1) →
      𝔼 x, f x ≤ 1 / 2 →
        ∑ S with S.card = 1, boolFourierCoeff n f S ^ 2 ≤
          C * (𝔼 x, f x) ^ 2 * Real.log (1 / 𝔼 x, f x) := by
  refine ⟨2 * Real.exp 1, fun n f hf hhalf => ?_⟩
  set α := 𝔼 x, f x with hα
  have hα0 : 0 ≤ α := Finset.expect_nonneg fun x _ => by rcases hf x with h | h <;> simp [h]
  rcases hα0.eq_or_lt with h0 | hpos
  · -- `α = 0`: `f = 0`, so every Fourier coefficient vanishes.
    have hz : ∀ x, f x = 0 := by
      intro x
      have hsum := (Finset.expect_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun y _ => by rcases hf y with h | h <;> simp [h])).mp h0.symm x (Finset.mem_univ x)
      exact hsum
    have hf0 : f = fun _ => 0 := funext hz
    rw [← h0]
    simp [hf0]
  · have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hL : Real.log 2 ≤ Real.log (1 / α) := by
      refine Real.log_le_log (by norm_num) ?_
      rw [le_div_iff₀ hpos]
      linarith
    have h1 := level_k_inequality hf le_rfl (by push_cast; linarith)
    have hsub : ∑ S with S.card = 1, boolFourierCoeff n f S ^ 2 ≤
        ∑ S with S.card ≤ 1, boolFourierCoeff n f S ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun S hS => Finset.mem_filter.mpr ⟨Finset.mem_univ S, (Finset.mem_filter.mp hS).2.le⟩)
        fun S _ _ => sq_nonneg _
    refine hsub.trans (h1.trans_eq ?_)
    rw [← hα]
    push_cast
    ring

end BooleanCube
