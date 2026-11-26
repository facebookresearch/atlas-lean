/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.HBCCalibrating

/-!
# Stone's square-root product bound for HBC-admissible tuples

Prove the square-root product bound for positive increasing HBC-admissible tuples.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 1.
-/

namespace MetaMathlibExt

private theorem log_factor_lt (z y : ℝ) (hz : 1 < z) (hy : 1 < y) (hne : z ≠ y) :
    Real.log (1 - 1 / z) - Real.log (1 - 1 / y) <
      (Real.log z - Real.log y) / (y - 1) := by
  have hz0 : 0 < z := by linarith
  have hy0 : 0 < y := by linarith
  have hz1 : 0 < z - 1 := sub_pos.mpr hz
  have hy1 : 0 < y - 1 := sub_pos.mpr hy
  have hsum : (y - 1) / y + 1 / y = 1 := by field_simp; ring
  have hneq : (z - 1) / (y - 1) ≠ 1 := by
    intro h
    have := (div_eq_one_iff_eq hy1.ne').mp h
    exact hne (by linarith)
  have hc := strictConcaveOn_log_Ioi.2
    (show (z - 1) / (y - 1) ∈ Set.Ioi 0 from div_pos hz1 hy1)
    (show (1 : ℝ) ∈ Set.Ioi 0 from zero_lt_one) hneq
    (div_pos hy1 hy0) (div_pos zero_lt_one hy0) hsum
  have havg : (y - 1) / y * ((z - 1) / (y - 1)) + 1 / y * 1 = z / y := by
    field_simp
    ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, havg] at hc
  rw [Real.log_div hz1.ne' hy1.ne', Real.log_div hz0.ne' hy0.ne',
    div_mul_eq_mul_div, div_lt_iff₀ hy0] at hc
  have hf (x : ℝ) (hx : 0 < x) : 1 - 1 / x = (x - 1) / x := by
    field_simp
  rw [hf z hz0, hf y hy0, Real.log_div hz1.ne' hz0.ne',
    Real.log_div hy1.ne' hy0.ne', lt_div_iff₀ hy1]
  nlinarith

private theorem log_factor_le (z y : ℝ) (hz : 1 < z) (hy : 1 < y) :
    Real.log (1 - 1 / z) - Real.log (1 - 1 / y) ≤
      (Real.log z - Real.log y) / (y - 1) := by
  by_cases h : z = y
  · simp [h]
  · exact (log_factor_lt z y hz hy h).le

private theorem calibrating_real (a d k : ℕ) (ha : 0 < a) (hd : 0 < d) (hk : 1 ≤ k) :
    let α : ℝ := (a + d) / d
    let n : ℕ → ℝ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (1 - 1 / n i) = (a : ℝ) / (a + d) ∧
      (∀ j, 1 ≤ j → j < k → ∏ i ∈ Finset.Icc 1 j, n i = (d / a) * (α ^ 2 ^ j - 1)) ∧
      ∏ i ∈ Finset.Icc 1 k, n i = (d / a) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1)) := by
  have h := hbcCalibrating_prod_identities a d k ha hd hk
  intro α n
  let αq : ℚ := (a + d) / d
  let nq : ℕ → ℚ := fun i => if i < k then 1 + αq ^ 2 ^ (i - 1) else αq ^ 2 ^ (k - 1)
  have hαq : (αq : ℝ) = α := by
    dsimp [αq, α]
    push_cast
    rfl
  have hn (i : ℕ) : (nq i : ℝ) = n i := by
    dsimp [nq, n, αq, α]
    split_ifs <;> push_cast <;> rfl
  change (∏ i ∈ Finset.Icc 1 k, (1 - 1 / nq i) = (a : ℚ) / (a + d)) ∧
    (∀ j, 1 ≤ j → j < k → ∏ i ∈ Finset.Icc 1 j, nq i = (d / a) * (αq ^ 2 ^ j - 1)) ∧
    ∏ i ∈ Finset.Icc 1 k, nq i = (d / a) * (αq ^ 2 ^ k - αq ^ 2 ^ (k - 1)) at h
  refine ⟨?_, ?_, ?_⟩
  · have hh := congrArg (fun q : ℚ => (q : ℝ)) h.1
    push_cast at hh
    simpa only [hn] using hh
  · intro j hj hjk
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (h.2.1 j hj hjk)
    push_cast at hh
    simpa only [hn, hαq] using hh
  · have hh := congrArg (fun q : ℚ => (q : ℝ)) h.2.2
    push_cast at hh
    simpa only [hn, hαq] using hh

private theorem quadratic_bound (A U B D : ℝ) (hD : 1 ≤ D) (hDU : D ≤ U)
    (h1 : (A + 1) ^ 2 ≤ B ^ 2) (hU : (A + U) ^ 2 ≤ U * B ^ 2) :
    (A + D) ^ 2 ≤ D * B ^ 2 := by
  by_cases hEq : U = 1
  · have h : D = 1 := by linarith
    simpa [h] using h1
  · have hu : 0 < U - 1 := sub_pos.mpr (lt_of_le_of_ne (hD.trans hDU) (Ne.symm hEq))
    by_contra h
    have hbad : (U - 1) * (D * B ^ 2 - (A + D) ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hu (by linarith)
    have hlow := mul_nonneg (sub_nonneg.mpr hDU) (sub_nonneg.mpr h1)
    have hupp := mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hU)
    have hmid := mul_nonneg (mul_nonneg hu.le (sub_nonneg.mpr hD)) (sub_nonneg.mpr hDU)
    nlinarith only [hlow, hupp, hmid, hbad]

private theorem next_parameter_sq (a d P t D : ℝ) (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hP : 0 < P) (ht : 1 ≤ t) (hprefix : a * P ≤ d * (t - 1))
    (hbase : (a + d) ^ 2 ≤ d ^ 2 * t) (hD : 1 ≤ D) (hupper : D ≤ d * P) :
    (a * P + D) ^ 2 ≤ D * (d * t) ^ 2 := by
  have hd0 : 0 ≤ d := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hAP : 0 ≤ a * P := mul_nonneg (by linarith) hP.le
  have hsmall : a * P + 1 ≤ d * t := by nlinarith
  have hPbound : P ≤ d * t := by nlinarith
  have h1 : (a * P + 1) ^ 2 ≤ (d * t) ^ 2 := by nlinarith
  have hbP : (a + d) ^ 2 * P ≤ d ^ 2 * t * (d * t) := by
    exact (mul_le_mul_of_nonneg_right hbase hP.le).trans
      (mul_le_mul_of_nonneg_left hPbound (mul_nonneg (sq_nonneg d) ht0))
  have h2 := mul_le_mul_of_nonneg_right hbP hP.le
  have hU : (a * P + d * P) ^ 2 ≤ (d * P) * (d * t) ^ 2 := by
    nlinarith only [h2]
  exact quadratic_bound (a * P) (d * P) (d * t) D hD hupper h1 hU

private theorem prod_factor_lt_of_prefix_lt (k : ℕ) (hk : 0 < k) (z y : ℕ → ℝ)
    (hz : ∀ i < k, 1 < z i) (hy : ∀ i < k, 1 < y i)
    (hmono : ∀ i < k, ∀ j < k, i ≤ j → y i ≤ y j)
    (hprefix : ∀ j, 1 ≤ j → j ≤ k → ∏ i ∈ Finset.range j, z i < ∏ i ∈ Finset.range j, y i) :
    ∏ i ∈ Finset.range k, (1 - 1 / z i) < ∏ i ∈ Finset.range k, (1 - 1 / y i) := by
  let g : ℕ → ℝ := fun i => if i < k then 1 / (y i - 1) else 0
  have hg0 : 0 ≤ g := by
    intro i
    dsimp [g]
    split_ifs with hi
    · exact div_nonneg zero_le_one (sub_pos.mpr (hy i hi)).le
    · exact le_rfl
  have hg : AntitoneOn g (Set.Iio k) := by
    intro i hi j hj hij
    change i < k at hi
    change j < k at hj
    simp only [g, ite_eq_left hi, ite_eq_left hj]
    exact div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr (hy i hi))
      (sub_le_sub_right (hmono i hi j hj hij) 1)
  have hsum : ∀ j ≤ k, ∑ i ∈ Finset.range j, (Real.log (z i) - Real.log (y i)) ≤ 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hlog := Real.log_le_log
        (Finset.prod_pos (fun i hi =>
          zero_lt_one.trans (hz i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))))
        (hprefix j (by omega) hj).le
      rw [Real.log_prod (fun i hi =>
          (zero_lt_one.trans (hz i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))).ne'),
        Real.log_prod (fun i hi =>
          (zero_lt_one.trans (hy i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))).ne')] at hlog
      rw [Finset.sum_sub_distrib]
      linarith
  have hab := Finset.sum_mul_le_mul_of_sum_range_le hsum hg0 hg
  simp only [zero_mul] at hab
  have hterm (i : ℕ) (hi : i ∈ Finset.range k) :
      Real.log (1 - 1 / z i) - Real.log (1 - 1 / y i) ≤
        (Real.log (z i) - Real.log (y i)) * g i := by
    simpa only [g, ite_eq_left (Finset.mem_range.mp hi), div_eq_mul_inv, one_mul] using
      log_factor_le (z i) (y i) (hz i (Finset.mem_range.mp hi)) (hy i (Finset.mem_range.mp hi))
  have hfirst : z 0 < y 0 := by simpa using hprefix 1 le_rfl hk
  have hstrict := Finset.sum_lt_sum hterm
    ⟨0, Finset.mem_range.mpr hk, by
      simpa only [g, ite_eq_left hk, div_eq_mul_inv, one_mul] using
        log_factor_lt (z 0) (y 0) (hz 0 hk) (hy 0 hk) hfirst.ne⟩
  have hfz (i : ℕ) (hi : i ∈ Finset.range k) : 0 < 1 - 1 / z i :=
    sub_pos.mpr ((div_lt_one₀ (zero_lt_one.trans (hz i (Finset.mem_range.mp hi)))).mpr
      (hz i (Finset.mem_range.mp hi)))
  have hfy (i : ℕ) (hi : i ∈ Finset.range k) : 0 < 1 - 1 / y i :=
    sub_pos.mpr ((div_lt_one₀ (zero_lt_one.trans (hy i (Finset.mem_range.mp hi)))).mpr
      (hy i (Finset.mem_range.mp hi)))
  rw [Finset.sum_sub_distrib, ← Real.log_prod (fun i hi => (hfz i hi).ne'),
    ← Real.log_prod (fun i hi => (hfy i hi).ne')] at hstrict
  exact (Real.log_lt_log_iff (Finset.prod_pos hfz) (Finset.prod_pos hfy)).mp (by linarith)

private theorem prefix_prod_eq_range {M : Type*} [CommMonoid M] (f : ℕ → M) (j : ℕ) :
    ∏ i ∈ Finset.Icc 1 j, f i = ∏ i ∈ Finset.range j, f (1 + i) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp

private theorem exists_bounded_prefix (k : ℕ) (hk : 1 ≤ k) (z y : ℕ → ℝ)
    (hz : ∀ i ∈ Finset.Icc 1 k, 1 < z i) (hy : ∀ i ∈ Finset.Icc 1 k, 1 < y i)
    (hmono : MonotoneOn y (Set.Icc 1 k))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / y i) ≤ ∏ i ∈ Finset.Icc 1 k, (1 - 1 / z i)) :
    ∃ j ∈ Finset.Icc 1 k, ∏ i ∈ Finset.Icc 1 j, y i ≤ ∏ i ∈ Finset.Icc 1 j, z i := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hlt := prod_factor_lt_of_prefix_lt k hk (fun i => z (1 + i)) (fun i => y (1 + i))
    (fun i hi => hz (1 + i) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    (fun i hi => hy (1 + i) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    (fun i hi j hj hij => hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    (fun j hj hjk => by simpa only [prefix_prod_eq_range] using h j (Finset.mem_Icc.mpr ⟨hj, hjk⟩))
  exact (not_lt_of_ge hle) (by simpa only [prefix_prod_eq_range] using hlt)

private theorem tuple_monotone (k : ℕ) (y : ℕ → ℕ)
    (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1)) :
    MonotoneOn y (Set.Icc 1 k) := by
  intro i hi j hj hij
  have hi1 : 1 ≤ i := hi.1
  have hchain : ∀ j, i ≤ j → j ≤ k → y i ≤ y j := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hjk
      exact (ih (by omega)).trans (hmono j (by omega) (by omega)).le
  exact hchain j hij hj.2

private theorem tuple_two_le (a d k : ℕ) (ha : 0 < a) (hd : 0 < d) (hk : 2 ≤ k)
    (y : ℕ → ℕ) (hy0 : 0 < y 1)
    (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    ∀ i ∈ Finset.Icc 1 k, 2 ≤ y i := by
  have hfirst : 2 ≤ y 1 := by
    by_contra h
    have hy1 : y 1 = 1 := by omega
    have hzero : ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (by simp [hy1])
    have hpos : 0 < (a : ℝ) / (a + d) := div_pos (by exact_mod_cast ha) (by positivity)
    rw [hzero] at hlt
    linarith
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  exact hfirst.trans (tuple_monotone k y hmono ⟨le_rfl, by omega⟩ hi' hi'.1)

private theorem power_difference_mono (x z : ℝ) (hx : 1 ≤ x) (hxz : x ≤ z)
    (k : ℕ) (hk : 1 ≤ k) :
    x ^ 2 ^ k - x ^ 2 ^ (k - 1) ≤ z ^ 2 ^ k - z ^ 2 ^ (k - 1) := by
  have he : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  rw [he, pow_mul, pow_mul]
  have hxpow : 1 ≤ x ^ 2 ^ (k - 1) := one_le_pow₀ hx
  have hzpow := pow_le_pow_left₀ (by linarith : 0 ≤ x) hxz (2 ^ (k - 1))
  nlinarith

private theorem parameter_facts (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    1 < ((a : ℝ) + d) / d ∧ 1 ≤ Real.sqrt d ∧
      ((a : ℝ) + d) / Real.sqrt d = (((a : ℝ) + d) / d) * Real.sqrt d ∧
      1 < ((a : ℝ) + d) / Real.sqrt d := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hs2 := Real.sq_sqrt hd0.le
  have hs1 : 1 ≤ Real.sqrt d := by nlinarith
  have hα : 1 < ((a : ℝ) + d) / d := (lt_div_iff₀ hd0).mpr (by linarith)
  have heq : ((a : ℝ) + d) / Real.sqrt d = (((a : ℝ) + d) / d) * Real.sqrt d := by
    field_simp
    nlinarith [mul_nonneg (by positivity : 0 ≤ (a : ℝ) + d) (sub_nonneg.mpr hs2.le),
      mul_nonneg (by positivity : 0 ≤ (a : ℝ) + d) (sub_nonneg.mpr hs2.ge)]
  refine ⟨hα, hs1, heq, ?_⟩
  rw [heq]
  nlinarith

private theorem scaled_power_difference (a d k : ℕ) (ha : 0 < a) (hd : 0 < d) (hk : 1 ≤ k) :
    (d : ℝ) * ((((a : ℝ) + d) / d) ^ 2 ^ k - (((a : ℝ) + d) / d) ^ 2 ^ (k - 1)) ≤
      (((a : ℝ) + d) / Real.sqrt d) ^ 2 ^ k - (((a : ℝ) + d) / Real.sqrt d) ^ 2 ^ (k - 1) := by
  obtain ⟨hα, hs, hβ, _⟩ := parameter_facts a d ha hd
  let u : ℝ := (((a : ℝ) + d) / d) ^ 2 ^ (k - 1)
  let v : ℝ := Real.sqrt d ^ 2 ^ (k - 1)
  have hu : 1 ≤ u := one_le_pow₀ hα.le
  have hv : 1 ≤ v := one_le_pow₀ hs
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  have hv2 : v ^ 2 = (d : ℝ) ^ 2 ^ (k - 1) := by
    dsimp [v]
    rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
  have hdv : (d : ℝ) ≤ v ^ 2 := by
    rw [hv2]
    simpa using pow_le_pow_right₀ hd1 (Nat.one_le_pow (k - 1) 2 (by decide))
  rw [hβ, he, pow_mul, pow_mul, mul_pow]
  change (d : ℝ) * (u ^ 2 - u) ≤ (u * v) ^ 2 - u * v
  have hnonneg : 0 ≤ u ^ 2 - u := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hdv hnonneg
  have hterm := mul_nonneg (by linarith : 0 ≤ u) (by nlinarith : 0 ≤ v ^ 2 - v)
  nlinarith only [hscale, hterm]

private theorem prod_prefix_split {M : Type*} [CommMonoid M] (f : ℕ → M)
    (j k : ℕ) (hjk : j ≤ k) :
    ∏ i ∈ Finset.Icc 1 k, f i =
      (∏ i ∈ Finset.Icc 1 j, f i) * ∏ i ∈ Finset.Icc 1 (k - j), f (j + i) := by
  rw [prefix_prod_eq_range, show k = j + (k - j) by omega, Finset.prod_range_add]
  simp only [prefix_prod_eq_range]
  congr 1
  apply Finset.prod_congr (by congr 1; omega)
  intro i _
  congr 1
  omega

private theorem product_ratio (k : ℕ) (y : ℕ → ℕ)
    (hy : ∀ i ∈ Finset.Icc 1 k, 1 ≤ y i) :
    ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) =
      ((∏ i ∈ Finset.Icc 1 k, (y i - 1) : ℕ) : ℝ) /
        ((∏ i ∈ Finset.Icc 1 k, y i : ℕ) : ℝ) := by
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_sub (hy i hi)]
  have hpos : (0 : ℝ) < y i := by exact_mod_cast (show 0 < y i by have := hy i hi; omega)
  field_simp
  simp

private theorem product_bound (a d k : ℕ) (ha : 0 < a) (hd : 0 < d) (hk : 1 ≤ k)
    (y : ℕ → ℕ) (hy0 : 0 < y 1)
    (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / Real.sqrt d) ^ 2 ^ k - ((a + d) / Real.sqrt d) ^ 2 ^ (k - 1) := by
  induction k using Nat.strong_induction_on generalizing a d y with
  | ind k ih =>
    let α : ℝ := (a + d) / d
    let n : ℕ → ℝ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hb0 : (0 : ℝ) < a + d := add_pos ha0 hd0
    obtain ⟨hα, hs, hβ, _⟩ := parameter_facts a d ha hd
    change 1 < α at hα
    by_cases hy1 : y 1 = 1
    · have hk1 : k = 1 := by
        by_contra h
        have hh := tuple_two_le a d k ha hd (by omega) y hy0 hmono hlt 1
          (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
        omega
      subst k
      have hid : (d : ℝ) * (α ^ 2 - α) = a * α := by
        dsimp [α]
        field_simp
        ring
      have hcal : (a : ℝ) ≤ (d : ℝ) * (α ^ 2 - α) := by
        rw [hid]
        nlinarith
      have hscale := scaled_power_difference a d 1 ha hd le_rfl
      norm_num only [Nat.sub_self, pow_zero, pow_one] at hscale
      exact (by simpa [hy1, α] using hcal.trans hscale)
    have hy2 : ∀ i ∈ Finset.Icc 1 k, 2 ≤ y i := by
      intro i hi
      have hm := tuple_monotone k y hmono ⟨le_rfl, hk⟩ (Finset.mem_Icc.mp hi)
        (Finset.mem_Icc.mp hi).1
      omega
    have hypos : ∀ i ∈ Finset.Icc 1 k, 0 < y i := by
      intro i hi
      have := hy2 i hi
      omega
    have hyR : ∀ i ∈ Finset.Icc 1 k, 1 < (y i : ℝ) := by
      intro i hi
      exact_mod_cast (show 1 < y i by have := hy2 i hi; omega)
    have hn : ∀ i ∈ Finset.Icc 1 k, 1 < n i := by
      intro i _
      dsimp [n]
      split_ifs
      · have := pow_pos (zero_lt_one.trans hα) (2 ^ (i - 1))
        linarith
      · exact one_lt_pow₀ hα (Nat.pow_pos (by decide)).ne'
    have hcal := calibrating_real a d k ha hd hk
    change (∏ i ∈ Finset.Icc 1 k, (1 - 1 / n i) = (a : ℝ) / (a + d)) ∧
      (∀ j, 1 ≤ j → j < k → ∏ i ∈ Finset.Icc 1 j, n i = (d / a) * (α ^ 2 ^ j - 1)) ∧
      ∏ i ∈ Finset.Icc 1 k, n i = (d / a) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1)) at hcal
    obtain ⟨j, hj, hprefix⟩ := exists_bounded_prefix k hk n (fun i => (y i : ℝ)) hn hyR
      (fun i hi j hj hij => by
        change (y i : ℝ) ≤ y j
        exact_mod_cast tuple_monotone k y hmono hi hj hij)
      (by simpa only [hcal.1] using hle)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    have hcancel : (a : ℝ) * (d / a) = d := by field_simp
    by_cases heq : j = k
    · subst j
      have hfull : a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
          (d : ℝ) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1)) := by
        calc
          a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ a * ∏ i ∈ Finset.Icc 1 k, n i :=
            mul_le_mul_of_nonneg_left hprefix ha0.le
          _ = (d : ℝ) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1)) := by
            rw [hcal.2.2, ← mul_assoc, hcancel]
      exact hfull.trans (scaled_power_difference a d k ha hd hk)
    have hjlt : j < k := by omega
    let P : ℕ := ∏ i ∈ Finset.Icc 1 j, y i
    let Q : ℕ := ∏ i ∈ Finset.Icc 1 j, (y i - 1)
    let A : ℕ := a * P
    let D : ℕ := (a + d) * Q - A
    have hyj : ∀ i ∈ Finset.Icc 1 j, 2 ≤ y i := fun i hi =>
      hy2 i (Finset.Icc_subset_Icc le_rfl hjk hi)
    have hP : 0 < P := Finset.prod_pos (fun i hi => by have := hyj i hi; omega)
    have hQ : 0 < Q := Finset.prod_pos (fun i hi => by have := hyj i hi; omega)
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hratio : ∏ i ∈ Finset.Icc 1 j, (1 - 1 / (y i : ℝ)) = (Q : ℝ) / P :=
      product_ratio j y (fun i hi => by have := hyj i hi; omega)
    have hgreater : (a : ℝ) / (a + d) < (Q : ℝ) / P := by
      rw [← hratio]
      refine hlt.trans_le (Finset.prod_le_prod_of_subset_of_le_one₀
        (Finset.Icc_subset_Icc le_rfl (by omega)) ?_ ?_)
      · intro i hi
        have hyi := hyR i (Finset.Icc_subset_Icc le_rfl (by omega : k - 1 ≤ k) hi)
        exact (sub_pos.mpr ((div_lt_one₀ (zero_lt_one.trans hyi)).mpr hyi)).le
      · intro i _ _
        exact sub_le_self 1 (by positivity)
    have hAnat : A < (a + d) * Q := by
      have hh := (div_lt_div_iff₀ hb0 hPr).mp hgreater
      dsimp [A]
      have hh' : a * P < Q * (a + d) := by exact_mod_cast hh
      simpa only [mul_comm] using hh'
    have hA : 0 < A := Nat.mul_pos ha hP
    have hD : 0 < D := by dsimp [D]; omega
    have hADnat : A + D = (a + d) * Q := by dsimp [D]; omega
    have hAD : (A : ℝ) + D = ((a : ℝ) + d) * Q := by exact_mod_cast hADnat
    have hQP : Q ≤ P := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
      (fun i _ => Nat.sub_le (y i) 1)
    have hupper : (D : ℝ) ≤ (d : ℝ) * P := by
      have hh : (Q : ℝ) ≤ P := by exact_mod_cast hQP
      have hh' := mul_le_mul_of_nonneg_left hh hb0.le
      have hAr : (A : ℝ) = a * (P : ℝ) := by simp [A]
      nlinarith
    have hprefixA : (a : ℝ) * P ≤ (d : ℝ) * (α ^ 2 ^ j - 1) := by
      have hh := mul_le_mul_of_nonneg_left hprefix ha0.le
      rw [hcal.2.1 j hj1 hjlt, ← mul_assoc, hcancel] at hh
      simpa only [P, Nat.cast_prod] using hh
    have hr : (A : ℝ) / (A + D) = ((a : ℝ) / (a + d)) / ((Q : ℝ) / P) := by
      rw [hAD]
      dsimp [A]
      push_cast
      field_simp
    have hle' : ∏ i ∈ Finset.Icc 1 (k - j), (1 - 1 / (y (j + i) : ℝ)) ≤
        (A : ℝ) / (A + D) := by
      rw [hr]
      apply (le_div_iff₀ (div_pos hQr hPr)).mpr
      rw [prod_prefix_split (fun i => 1 - 1 / (y i : ℝ)) j k hjk, hratio] at hle
      simpa only [mul_comm] using hle
    have hlt' : (A : ℝ) / (A + D) <
        ∏ i ∈ Finset.Icc 1 (k - j - 1), (1 - 1 / (y (j + i) : ℝ)) := by
      rw [hr]
      apply (div_lt_iff₀ (div_pos hQr hPr)).mpr
      rw [prod_prefix_split (fun i => 1 - 1 / (y i : ℝ)) j (k - 1) (by omega), hratio] at hlt
      simpa only [show k - 1 - j = k - j - 1 by omega, mul_comm] using hlt
    have htail := ih (k - j) (by omega) A D hA hD (by omega) (fun i => y (j + i))
      (hypos (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      (fun i hi hik => hmono (j + i) (by omega) (by omega)) hle' hlt'
    have he2 : 2 ≤ 2 ^ j := by
      simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hj1
    have ht : 1 ≤ α ^ 2 ^ j := one_le_pow₀ hα.le
    have hαeq : (d : ℝ) * α = (a : ℝ) + d := by dsimp [α]; field_simp
    have hbase : ((a : ℝ) + d) ^ 2 ≤ (d : ℝ) ^ 2 * α ^ 2 ^ j := by
      calc
        ((a : ℝ) + d) ^ 2 = (d : ℝ) ^ 2 * α ^ 2 := by rw [← mul_pow, hαeq]
        _ ≤ (d : ℝ) ^ 2 * α ^ 2 ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα.le he2) (sq_nonneg (d : ℝ))
    have hnext := next_parameter_sq (a : ℝ) (d : ℝ) (P : ℝ) (α ^ 2 ^ j) (D : ℝ)
      (by exact_mod_cast ha) (by exact_mod_cast hd) hPr ht hprefixA hbase
      (by exact_mod_cast hD) hupper
    have hAr : (A : ℝ) = a * (P : ℝ) := by simp [A]
    rw [← hAr] at hnext
    have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast hD)
    have hsq : ((d : ℝ) * α ^ 2 ^ j * Real.sqrt D) ^ 2 =
        ((d : ℝ) * α ^ 2 ^ j) ^ 2 * D := by rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hnextle : ((A : ℝ) + D) / Real.sqrt D ≤ (d : ℝ) * α ^ 2 ^ j := by
      apply (div_le_iff₀ hsD).mpr
      have hnonneg : 0 ≤ (d : ℝ) * α ^ 2 ^ j * Real.sqrt D := by positivity
      nlinarith only [hnext, hsq, hnonneg]
    have hds : (d : ℝ) ≤ Real.sqrt d ^ 2 ^ j := by
      exact (Real.sq_sqrt hd0.le).symm.trans_le (pow_le_pow_right₀ hs he2)
    have hparameter : ((A : ℝ) + D) / Real.sqrt D ≤
        (((a : ℝ) + d) / Real.sqrt d) ^ 2 ^ j := by
      refine hnextle.trans ?_
      rw [hβ, mul_pow]
      change (d : ℝ) * α ^ 2 ^ j ≤ α ^ 2 ^ j * Real.sqrt d ^ 2 ^ j
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hds (zero_le_one.trans ht)
    have hmonoF := power_difference_mono _ _ (parameter_facts A D hA hD).2.2.2.le
      hparameter (k - j) (by omega)
    have heleft : 2 ^ j * 2 ^ (k - j) = 2 ^ k := by rw [← pow_add]; congr 1; omega
    have heright : 2 ^ j * 2 ^ (k - j - 1) = 2 ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    rw [← pow_mul, ← pow_mul, heleft, heright] at hmonoF
    rw [prod_prefix_split (fun i => (y i : ℝ)) j k hjk]
    simpa only [hAr, P, Nat.cast_prod, mul_assoc] using htail.trans hmonoF

@[expose] public section

/-- **Stone's $\sqrt{d}$ product bound for HBC-admissible tuples.** Let $a$ and $d$ be coprime
positive integers, let $k \ge 1$, and let $y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le a/(a + d) < \prod_{i=1}^{k-1} (1 - 1/y_i)$. Put
$\beta = (a + d)/\sqrt{d}$. Then $a \prod_{i=1}^{k} y_i \le \beta^{2^k} - \beta^{2^{k-1}}$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 1. -/
public theorem hbcAdmissible_prod_le_sqrt (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcop : Nat.Coprime a d) (hk : 1 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1)
    (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / Real.sqrt d) ^ 2 ^ k - ((a + d) / Real.sqrt d) ^ 2 ^ (k - 1)
    := by
  have _ := hcop
  exact product_bound a d k ha hd hk y hy0 hmono hle hlt

end

end MetaMathlibExt
