/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Logic.Equiv.Nat
import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import MathlibExt.NumberTheory.BridgemanPellNegativeSeries
import MathlibExt.NumberTheory.SanfordSymmetricSeries

open MetaMathlibExt Real

private noncomputable abbrev L (x : ℝ) : ℝ :=
  (∑' j : ℕ, x ^ (j + 1) / ((j : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2

private def unit₂ : ℤ√(2 : ℤ) := ⟨1, 1⟩

private def A (k : ℕ) : ℚ := (unit₂ ^ k).re
private def B (k : ℕ) : ℚ := (unit₂ ^ k).im

-- Verify the entire series at 1 + √2 without the theorem under test. Use the two
-- real embeddings of ℤ[√2] to read off the coefficients directly from ring powers.
example : L (1 / (1 + √2) ^ 2) =
    (∑' k : ℕ, L (1 / (2 * (B (2 * (k + 1)) : ℝ) ^ 2))) +
      ∑' k : ℕ, L (1 / (A (2 * (k + 1) + 1) : ℝ) ^ 2) := by
  let R := √(2 : ℝ)
  have hR : R ^ 2 = 2 := sq_sqrt (by norm_num)
  have hR₁ : 1 < R := by nlinarith [sqrt_nonneg (2 : ℝ)]
  let u := 1 + R
  let v := R - 1
  let t := R / 2
  let x := 1 / 2 - t / 2
  let y := 1 / 2 + t / 2
  let c := 2 * R
  have ht₀ : 0 < t := by dsimp only [t]; linarith
  have ht₁ : t < 1 := by dsimp only [t]; nlinarith
  have hc : c ≠ 0 := by dsimp only [c]; positivity
  have hu : u ≠ 0 := by dsimp only [u]; positivity
  have huv : u * v = 1 := by dsimp only [u, v]; nlinarith
  have hratio : (1 - t) / (1 + t) = 1 / u ^ 2 := by
    have hy : 1 + t ≠ 0 := by positivity
    field_simp [hu, hy]
    dsimp only [t, u]
    linear_combination (-R / 2) * hR
  have hx : x * c = v := by dsimp only [x, c, t, v]; nlinarith
  have hy : y * c = u := by dsimp only [y, c, t, u]; nlinarith
  let f (k : ℕ) := L (t ^ 2 * x ^ (k + 1) * y ^ (k + 1) / (y ^ (k + 2) - x ^ (k + 2)) ^ 2)
  have hsum : (∑' k, f k) = L ((1 - t) / (1 + t)) :=
    rogersDilog_sanford_symmetric_series ht₀ ht₁
  have hf (k : ℕ) : f k = L (4 / (u ^ (k + 2) - v ^ (k + 2)) ^ 2) := by
    have htc : t * c = 2 := by dsimp only [t, c]; nlinarith
    have hxy : x * y * c ^ 2 = 1 := by
      rw [show x * y * c ^ 2 = (y * c) * (x * c) by ring, hx, hy, huv]
    have hnum : (t ^ 2 * x ^ (k + 1) * y ^ (k + 1)) * (c ^ (k + 2)) ^ 2 = 4 := by
      rw [show k + 2 = (k + 1) + 1 by rfl, pow_succ c, mul_pow, ← pow_mul, Nat.mul_comm (k + 1),
        pow_mul, mul_assoc (t ^ 2), ← mul_pow x y]
      calc
        _ = (t * c) ^ 2 * (x * y * c ^ 2) ^ (k + 1) := by rw [mul_pow t, mul_pow (x * y)]; ring
        _ = 4 := by rw [htc, hxy, one_pow, mul_one]; norm_num
    have hden : (y ^ (k + 2) - x ^ (k + 2)) * c ^ (k + 2) = u ^ (k + 2) - v ^ (k + 2) := by
      rw [sub_mul, ← mul_pow, ← mul_pow, hx, hy]
    dsimp only [f]
    rw [← mul_div_mul_right _ _ (pow_ne_zero 2 (pow_ne_zero _ hc)), hnum, ← mul_pow, hden]
  let φ := Zsqrtd.toReal (d := 2) (by decide)
  have hφ (j : ℕ) : ((A j : ℝ) + (B j : ℝ) * R) = u ^ j := by
    simpa [φ, unit₂, A, B, u, R] using (map_pow φ unit₂ j)
  have hφ' (j : ℕ) : ((A j : ℝ) - (B j : ℝ) * R) = (-v) ^ j := by
    have h := map_pow φ (star unit₂) j
    rw [← star_pow] at h
    simp only [φ, Zsqrtd.toReal_apply, Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg] at h
    simpa [unit₂, A, B, v, R, sub_eq_add_neg, neg_add_rev, add_comm, mul_comm] using h
  have he (k : ℕ) : f (2 * k) = L (1 / (2 * (B (2 * (k + 1)) : ℝ) ^ 2)) := by
    let j := 2 * (k + 1)
    have hneg := (even_two_mul (k + 1)).neg_pow v
    have h : u ^ j - v ^ j = 2 * ((B j : ℝ) * R) := by linarith [hφ j, hφ' j, hneg]
    rw [hf, show 2 * k + 2 = j by dsimp only [j]; omega, h, mul_pow, mul_pow, hR]
    congr 1
    ring
  have ho (k : ℕ) : f (2 * k + 1) = L (1 / (A (2 * (k + 1) + 1) : ℝ) ^ 2) := by
    let j := 2 * (k + 1) + 1
    have hneg := (odd_two_mul_add_one (k + 1)).neg_pow v
    have h : u ^ j - v ^ j = 2 * (A j : ℝ) := by linarith [hφ j, hφ' j, hneg]
    rw [hf, show 2 * k + 1 + 2 = j by dsimp only [j]; omega, h, mul_pow]
    congr 1
    ring
  have hs : Summable f := by
    have hr₀ : 0 < (1 - t) / (1 + t) := by positivity
    have hr₁ : (1 - t) / (1 + t) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have hrLog : 0 < log ((1 - t) / (1 + t)) * log (1 - (1 - t) / (1 + t)) / 2 :=
      div_pos (mul_pos_of_neg_of_neg (log_neg hr₀ hr₁)
        (log_neg (sub_pos.mpr hr₁) (sub_lt_self _ hr₀))) (by norm_num)
    have hrL : 0 < L ((1 - t) / (1 + t)) :=
      add_pos_of_nonneg_of_pos (tsum_nonneg fun _ => by positivity) hrLog
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at hsum
    exact hrL.ne' hsum.symm
  let e := Equiv.natSumNatEquivNat
  have hparts := Summable.tsum_sum (f := f ∘ e)
    (hs.comp_injective (e.injective.comp Sum.inl_injective))
    (hs.comp_injective (e.injective.comp Sum.inr_injective))
  rw [← show 1 / u ^ 2 = 1 / (1 + √2) ^ 2 by rfl, ← hratio, ← hsum, ← e.tsum_eq f]
  simpa only [e, Function.comp_apply, Equiv.natSumNatEquivNat_apply, Sum.elim_inl,
    Sum.elim_inr, he, ho] using hparts

-- At the nontrivial solution 7 + 5√2, the two branches have distinct integral
-- quotients. Check the boundary index k = 0 and the first series index k = 1.
example : let z : ℤ√(2 : ℤ) := ⟨7, 5⟩
    (z ^ 0).im = 7 * 0 ∧ (z ^ 1).re = 7 * 1 ∧
      (z ^ 2).im = 7 * 10 ∧ (z ^ 3).re = 7 * 199 := by decide

-- A client can use both conclusions with rational coordinates of ring powers.
example (k : ℕ) : L (1 / (1 + √2) ^ 2) =
    (∑' j : ℕ, L (1 / (2 * (B (2 * (j + 1)) : ℝ) ^ 2))) +
      ∑' j : ℕ, L (1 / (A (2 * (j + 1) + 1) : ℝ) ^ 2) ∧
    ((∃ m : ℤ, B (2 * k) = (m : ℚ)) ∧ ∃ m : ℤ, A (2 * k + 1) = (m : ℚ)) := by
  have hn : ¬ IsSquare (2 : ℕ) := by
    simp [IsSquare, eq_comm, Nat.exists_mul_self]
  have hA (j : ℕ) : A (j + 1) = 1 * A j + 2 * 1 * B j := by
    simp [A, B, pow_succ, unit₂]
  have hB (j : ℕ) : B (j + 1) = 1 * A j + 1 * B j := by
    simp [A, B, pow_succ, unit₂]
  have h := rogersDilog_pell_negative_series (n := 2) hn (a := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (A := A) (B := B)
    (by simp [A]) (by simp [B]) hA hB
  refine ⟨?_, ?_⟩
  · simpa only [Rat.cast_one, Nat.cast_ofNat, one_mul, one_pow] using h.1
  · simpa only [one_mul] using h.2 ⟨1, 1, by norm_num, by norm_num⟩ k
