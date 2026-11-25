/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLInequality
import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize

/-!
# The KKL inequality for biased Boolean cubes

For each Bernoulli bias `0 < p < 1`, `kkl_pbiased` proves the Kahn–Kalai–Linial inequality
with a positive constant depending only on `p`. The proof combines biased Fourier
representations of variance and total influence with a capped hypercontractive estimate.
-/

namespace MathlibExt.Complexity.BooleanFunctions.KKLPBiasedWanted

open Finset StatMech StatMech.OSSS StatMech.Probability

/-- **KKL inequality for `p`-biased measures** (Bourgain–Kahn–Kalai–Katznelson–Linial;
Talagrand). For every `p ∈ (0, 1)` there is `c > 0` such that for every finite nonempty `E` and
every Boolean function `φ` on `{0, 1}^E`,
`c · Var_p(φ) · log (1 / maxₑ Infₑ^p(φ)) ≤ ∑ₑ Infₑ^p(φ)`, where `Infₑ^p(φ)` is the probability
under the Bernoulli(`p`) product measure that `e` is pivotal for `φ`.

Talagrand's inequality `Var_p(φ) ≤ K(p) ∑ₑ Infₑ / log (1 / (p (1 - p) Infₑ))` gives this with
`c = 1 / K(p)`, since each `Infₑ ≤ maxₑ Infₑ`.

Source: M. Talagrand, *On Russo's approximate zero-one law*, Ann. Probab. 22 (1994);
J. Bourgain, J. Kahn, G. Kalai, Y. Katznelson, N. Linial, *The influence of variables in product
spaces*, Israel J. Math. 77 (1992). -/
public theorem kkl_pbiased :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ c : ℝ, 0 < c ∧ KKLHypercontractive p c := by
  intro p hp0 hp1
  let s := p * (1 - p)
  let b := 2 * s
  let a := -Real.log b
  have hs : 0 < s := mul_pos hp0 (sub_pos.mpr hp1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b, s]; nlinarith [sq_nonneg (p - 1 / 2)]
  have ha : 0 ≤ a := neg_nonneg.mpr (Real.log_nonpos hb.le hb1)
  have hconstant : 0 < 3 * (a + 1) * s := by positivity
  refine ⟨1 / (3 * (a + 1) * s), by positivity, ?_⟩
  intro E _ _ _ φ
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let δ := maxInfl (bernoulliWeight p) f
  let T := totalInfl (bernoulliWeight p) f
  change 1 / (3 * (a + 1) * s) * var (bernoulliWeight p) f * Real.log (1 / δ) ≤ T
  have hprob := bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
  rcases eq_or_lt_of_le (kkl_maxInfl_nonneg hprob f : 0 ≤ δ) with hδ | hδ
  · change 0 = δ at hδ
    rw [← hδ, div_zero, Real.log_zero, mul_zero]
    exact kkl_totalInfl_nonneg hprob f
  let L := -Real.log δ
  let d := δ ^ (1 / 3 : ℝ)
  have hd : 0 < d := Real.rpow_pos_of_pos hδ _
  let w (S : Finset E) := (ptn_coeff p f S) ^ 2
  let u (S : Finset E) := (S.card : ℝ) * w S
  let v (S : Finset E) := (S.card : ℝ) * (b ^ (S.card - 1) * w S)
  have hT : (∑ S, u S) = s * T := by
    have h := ptn_totalInfl_eq_fourierWeight hp0 hp1 φ
    rw [ptn_sigma_sq hp0 hp1] at h
    change T = (1 / s) * ∑ S, u S at h
    rw [one_div, ← div_eq_inv_mul, eq_div_iff hs.ne'] at h
    simpa only [mul_comm T s] using h.symm
  have hV : (∑ S, v S) ≤ s * (d * T) := by
    have hρsq : (Real.sqrt b) ^ 2 = ((3 / 2 : ℝ) - 1) * 4 * p * (1 - p) := by
      rw [Real.sq_sqrt hb.le]
      dsimp [b, s]
      ring
    have h := ptn_capped_hc hp0 hp1 (Real.sqrt_nonneg b) (Real.sqrt_le_one.mpr hb1)
      (by norm_num) (by norm_num) hρsq φ
    have hpow (n : ℕ) : (Real.sqrt b ^ n) ^ 2 = b ^ n := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hb.le]
    simp only [hpow, ptn_sigma_sq hp0 hp1, show (2 : ℝ) / (3 / 2) - 1 = 1 / 3 by norm_num] at h
    change (1 / s) * (∑ S, v S) ≤ d * T at h
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hs, mul_comm (d * T) s] at h
    exact h
  -- The exponential bound turns the noise weight at each nonzero degree into a log estimate.
  have hterm (S : Finset E) (hS : S ∈ univ.erase (∅ : Finset E)) :
      L * w S ≤ 3 * a * u S + (3 / d) * v S := by
    have hn : (1 : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase hS))
    have hk : ((S.card - 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have heq : Real.exp (L / 3 - a * (S.card - 1 : ℕ)) = b ^ (S.card - 1) / d := by
      rw [show L / 3 - a * (S.card - 1 : ℕ) =
        Real.log b * ↑(S.card - 1) - Real.log δ * (1 / 3) by dsimp [L, a]; ring,
        Real.exp_sub, ← Real.rpow_def_of_pos hb, Real.rpow_natCast,
        ← Real.rpow_def_of_pos hδ]
    have hexp := Real.add_one_le_exp (L / 3 - a * (S.card - 1 : ℕ))
    rw [heq] at hexp
    have hdeg := mul_le_mul_of_nonneg_left hk ha
    have hnoise := mul_le_mul_of_nonneg_right hn
      (show 0 ≤ b ^ (S.card - 1) / d by positivity)
    rw [one_mul] at hnoise
    have hpoint : L ≤ 3 * a * (S.card : ℝ) + (3 / d) * ((S.card : ℝ) * b ^ (S.card - 1)) := by
      calc
        L ≤ 3 * (a * (S.card - 1 : ℕ) + b ^ (S.card - 1) / d) := by linarith only [hexp]
        _ ≤ 3 * (a * (S.card : ℝ) + (S.card : ℝ) * (b ^ (S.card - 1) / d)) :=
          mul_le_mul_of_nonneg_left (add_le_add hdeg hnoise) (by norm_num)
        _ = _ := by ring
    calc
      L * w S ≤ (3 * a * (S.card : ℝ) + (3 / d) * ((S.card : ℝ) * b ^ (S.card - 1))) * w S :=
        mul_le_mul_of_nonneg_right hpoint (sq_nonneg _)
      _ = _ := by dsimp [u, v]; ring
  have hsum :
      L * var (bernoulliWeight p) f ≤ 3 * a * (∑ S, u S) + (3 / d) * (∑ S, v S) := by
    rw [ptn_var_eq_fourierWeight hp0 hp1, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    exact (sum_le_sum hterm).trans
      (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun S _ _ => by
        dsimp [u, v, w]
        positivity))
  calc
    _ = (L * var (bernoulliWeight p) f) / (3 * (a + 1) * s) := by
      rw [one_div, Real.log_div one_ne_zero hδ.ne', Real.log_one, zero_sub]
      change _ * _ * L = _
      ring
    _ ≤ T := by
      apply (div_le_iff₀ hconstant).2
      calc
        L * var (bernoulliWeight p) f
            ≤ 3 * a * (s * T) + (3 / d) * (s * (d * T)) := by
          rw [← hT]
          exact hsum.trans (add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hV (show 0 ≤ 3 / d by positivity)))
        _ = _ := by field_simp

end MathlibExt.Complexity.BooleanFunctions.KKLPBiasedWanted
