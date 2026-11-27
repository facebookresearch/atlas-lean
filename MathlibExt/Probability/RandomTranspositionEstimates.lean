/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Spectral sum estimates for random transpositions

Diaconis and Shahshahani bound the mixing time for random transpositions by summing even
powers of the eigenvalues. This module supplies the numerical step in that argument:
`cutoff_of_spectrum` takes eigenvalues listed with multiplicity, an upper bound indexed by
first-row deficit, and a count for each deficit in each sign class. It bounds twice total
variation by `2 * exp 3 * n * exp (-2 * k / n)` whenever the spectral moment bounds its square.

Put `d = 2k/n - log n`. At `d ≥ 3`, each positive deficit `j` contributes at most
`exp (-j) * exp (-2 * (d - 3))` per sign class. The proof uses the chord of `exp` between
`0` and `log n` to absorb the loss in the spectral bound into the factorial in the level count.
The two level-zero terms are treated separately. At `d < 3`, the trivial bound suffices.

Source: P. Diaconis and M. Shahshahani, *Generating a random permutation with random
transpositions*, Z. Wahrsch. Verw. Gebiete **57** (1981), 159–179, Theorem 1 and §3.
The chord estimate below is an alternative summation argument; the constant is not optimal.
-/

@[expose] public section

namespace MathlibExt.Probability.RandomTranspositionEstimates

open Finset Real

/-- The minimum of `1 - 2j(n-j+1)/n²` and `1 - j/n`. For `n > 0`, these are the two
upper bounds for the normalised transposition eigenvalue at symmetriser deficit `j` given by
`MathlibExt.Probability.RandomTranspositionFiltration.exists_level_bounds_univ`. -/
noncomputable def cap (n j : ℕ) : ℝ :=
  min (1 - 2 * j * ((n : ℝ) - j + 1) / (n : ℝ) ^ 2) (1 - (j : ℝ) / n)

/-- At deficit zero the spectral bound equals one. -/
@[simp] theorem cap_zero (n : ℕ) : cap n 0 = 1 := by simp [cap]

/-- Keep a nonnegative eigenvalue and replace a negative one by the eigenvalue of its
sign twist. Twisting negates the transposition character and leaves the holding mass `1/n`
unchanged (Diaconis and Shahshahani, 1981, Corollary 1 and Lemma 8, (2.10)). -/
noncomputable def oriented (n : ℕ) (x : ℝ) : ℝ := if 0 ≤ x then x else 2 / (n : ℝ) - x

private theorem cap_nonneg {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) :
    0 ≤ cap n j := by
  have hN : 0 < (n : ℝ) := by positivity
  have hJ : (j : ℝ) ≤ n := by exact_mod_cast hjn
  apply le_min
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ (sq_pos_of_pos hN)).2
    by_cases hj1 : j = 1
    · subst j
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith [mul_nonneg hN.le (sub_nonneg.mpr h2)]
    · have h2 : (2 : ℝ) ≤ j := by exact_mod_cast (by omega : 2 ≤ j)
      nlinarith [sq_nonneg ((n : ℝ) - j),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (sub_nonneg.mpr h2)]
  · exact sub_nonneg.mpr ((div_le_one hN).mpr hJ)

private theorem level_count_le (n j : ℕ) :
    (n.choose j : ℝ) * (n : ℝ) ^ j ≤ (n : ℝ) ^ (2 * j) / (j.factorial : ℝ) := by
  have hf : 0 < (j.factorial : ℝ) := by positivity
  have h := Nat.descFactorial_le_pow n j
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hc : (j.factorial : ℝ) * (n.choose j : ℝ) ≤ (n : ℝ) ^ j := by exact_mod_cast h
  rw [le_div_iff₀ hf, two_mul, pow_add]
  calc
    _ = ((j.factorial : ℝ) * (n.choose j : ℝ)) * (n : ℝ) ^ j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- Bound a single positive deficit. The effective exponent `b` pays for both the geometric
sum (`b ≥ j`) and the sharp decay after the fixed shift (`b ≥ 2`). -/
private theorem deficit_term {n j k : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hd : 3 ≤ 2 * (k : ℝ) / n - log n) :
    (n : ℝ) ^ (2 * j) / (j.factorial : ℝ) * cap n j ^ (2 * k) ≤
      exp (-(j : ℝ)) * exp (-2 * (2 * (k : ℝ) / n - log n - 3)) := by
  let J : ℝ := j
  let N : ℝ := n
  let d := 2 * (k : ℝ) / N - log N
  let a := min (2 * (J - 1) / N) 1
  let b := (2 - a) * J
  have hN : 0 < N := by dsimp [N]; positivity
  have hJ : 1 ≤ J := by dsimp [J]; exact_mod_cast hj
  have hJ0 : 0 ≤ J := by linarith
  have hd' : 3 ≤ d := hd
  have ha0 : 0 ≤ a := le_min (div_nonneg (by linarith) hN.le) zero_le_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have haN : a * N ≤ 2 * (J - 1) := (le_div_iff₀ hN).mp (min_le_left _ _)
  have hbj : J ≤ b := by
    dsimp [b]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hJ0]
  have hb2 : 2 ≤ b := by
    by_cases hj1 : j = 1
    · simp [b, a, J, hj1]
    · exact le_trans (by dsimp [J]; exact_mod_cast (by omega : 2 ≤ j)) hbj
  have hc : cap n j ≤ 1 - b / N := by
    rcases le_total (2 * (J - 1) / N) 1 with h | h
    · apply (min_le_left _ _).trans
      change 1 - 2 * J * (N - J + 1) / N ^ 2 ≤ 1 - (2 - a) * J / N
      rw [show a = 2 * (J - 1) / N from min_eq_left h]
      field_simp [hN.ne']
      ring_nf
      rfl
    · apply (min_le_right _ _).trans
      change 1 - J / N ≤ 1 - (2 - a) * J / N
      rw [show a = 1 from min_eq_right h]
      norm_num
  have hce : cap n j ≤ exp (-b / N) := hc.trans (by
    simpa [neg_div, sub_eq_add_neg, add_comm] using add_one_le_exp (-b / N))
  have hpow : cap n j ^ (2 * k) ≤ exp (-(log N + d) * b) := by
    calc
      _ ≤ exp (-b / N) ^ (2 * k) := pow_le_pow_left₀ (cap_nonneg hn hj hjn) hce _
      _ = _ := by rw [← exp_nat_mul]; congr 1; dsimp [d]; push_cast; ring
  -- The chord inequality gives `n ^ a ≤ 1 - a + a * n ≤ 2 * j`.
  have hchord := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (log N))
    (sub_nonneg.mpr ha1) ha0 (show 1 - a + a = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one, exp_log hN] at hchord
  have hae : exp (a * log N) ≤ 2 * J := by linarith
  have hf : 0 < (j.factorial : ℝ) := by positivity
  have hmass : N ^ (2 * j) = exp (2 * J * log N) := by
    conv_lhs => rw [← exp_log hN]
    rw [← exp_nat_mul]; push_cast; rfl
  change N ^ (2 * j) / (j.factorial : ℝ) * cap n j ^ (2 * k) ≤ _
  calc
    _ ≤ N ^ (2 * j) / (j.factorial : ℝ) * exp (-(log N + d) * b) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = exp (a * log N) ^ j / (j.factorial : ℝ) * exp (-d * b) := by
      rw [hmass, ← exp_nat_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, ← exp_add, ← exp_add]
      congr 2
      change 2 * J * log N + -(log N + d) * b = J * (a * log N) + -d * b
      dsimp [b]
      ring
    _ ≤ (2 * J) ^ j / (j.factorial : ℝ) * exp (-d * b) := by gcongr
    _ ≤ exp (2 * J) * exp (-d * b) := by
      gcongr
      exact pow_div_factorial_le_exp _ (by positivity) _
    _ ≤ exp (-J) * exp (-2 * (d - 3)) := by
      rw [← exp_add, ← exp_add, exp_le_exp]
      nlinarith [mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hd')]

private theorem sum_exp_neg_le_one (n : ℕ) : ∑ j ∈ Icc 1 n, exp (-(j : ℝ)) ≤ 1 := by
  have he : exp (-1) ≤ 1 / 2 := by
    rw [exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [add_one_le_exp 1])
  calc
    _ ≤ ∑ j ∈ Icc 1 n, (1 / 2 : ℝ) ^ j := by
      refine sum_le_sum fun j _ ↦ ?_
      simpa [← exp_nat_mul] using pow_le_pow_left₀ (exp_pos (-1)).le he j
    _ ≤ 1 := by
      rw [← Ico_add_one_right_eq_Icc, geom_sum_Ico (by norm_num : (1 / 2 : ℝ) ≠ 1) (by omega)]
      norm_num
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) (n + 1)]

private theorem deficit_sum {n k : ℕ} (hn : 2 ≤ n) (hd : 3 ≤ 2 * (k : ℝ) / n - log n) :
    ∑ j ∈ Icc 1 n, ((n.choose j : ℝ) * (n : ℝ) ^ j) * cap n j ^ (2 * k) ≤
      exp (-2 * (2 * (k : ℝ) / n - log n - 3)) := by
  set E := exp (-2 * (2 * (k : ℝ) / n - log n - 3))
  calc
    _ ≤ ∑ j ∈ Icc 1 n, exp (-(j : ℝ)) * E := by
      refine sum_le_sum fun j hj ↦ ?_
      obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      exact (mul_le_mul_of_nonneg_right (level_count_le n j)
        (pow_nonneg (cap_nonneg hn h1 h2) _)).trans (deficit_term hn h1 h2 hd)
    _ ≤ E := by
      rw [← sum_mul]
      exact mul_le_of_le_one_left (exp_pos _).le (sum_exp_neg_le_one n)

/-- Sum one sign class, retaining its own level-zero bound. -/
private theorem class_sum_le {ι : Type*} {n k : ℕ} (s : Finset ι) (level : ι → ℕ)
    (f : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hl : ∀ i ∈ s, level i ≤ n)
    (hzero : ∀ i ∈ s, level i = 0 → f i ≤ C)
    (hpos : ∀ i ∈ s, 1 ≤ level i → f i ≤ cap n (level i) ^ (2 * k))
    (hc : ∀ j ≤ n, (s.filter (fun i ↦ level i = j)).card ≤ n.choose j * n ^ j) :
    ∑ i ∈ s, f i ≤ C + ∑ j ∈ Icc 1 n, ((n.choose j : ℝ) * (n : ℝ) ^ j) * cap n j ^ (2 * k) := by
  let B : ℕ → ℝ := fun j ↦ if j = 0 then C else cap n j ^ (2 * k)
  have hf (i) (hi : i ∈ s) : f i ≤ B (level i) := by
    by_cases h : level i = 0
    · simpa [B, h] using hzero i hi h
    · simpa [B, h] using hpos i hi (by omega)
  have hB (j : ℕ) : 0 ≤ B j := by
    dsimp [B]
    split_ifs
    · exact hC
    · rw [pow_mul]; positivity
  have hmap : ∀ i ∈ s, level i ∈ Icc 0 n := fun i hi ↦ mem_Icc.mpr ⟨Nat.zero_le _, hl i hi⟩
  calc
    _ = ∑ j ∈ Icc 0 n, ∑ i ∈ s with level i = j, f i := (sum_fiberwise_of_maps_to hmap f).symm
    _ ≤ ∑ j ∈ Icc 0 n, ((n.choose j : ℝ) * (n : ℝ) ^ j) * B j := by
      refine sum_le_sum fun j hj ↦ ?_
      have hcard : ((s.filter (fun i ↦ level i = j)).card : ℝ) ≤ (n.choose j : ℝ) * (n : ℝ) ^ j :=
        by exact_mod_cast hc j (mem_Icc.mp hj).2
      have hsum := sum_le_card_nsmul (s.filter (fun i ↦ level i = j)) f (B j) (fun i hi ↦ by
        obtain ⟨hiS, hji⟩ := mem_filter.mp hi
        simpa only [← hji] using hf i hiS)
      rw [nsmul_eq_mul] at hsum
      exact hsum.trans (mul_le_mul_of_nonneg_right hcard (hB j))
    _ = _ := by
      rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le n), zero_add, sum_insert (by simp)]
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, B, ite_true]
      congr 1
      refine sum_congr rfl fun j hj ↦ ?_
      have hj0 : j ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hj).1
      simp [hj0]

private theorem spectrum_sum_le {ι : Type*} [Fintype ι] {n k : ℕ} (hn : 2 ≤ n)
    (v : ι → ℝ) (level : ι → ℕ) (hl : ∀ i, level i ≤ n)
    (hcap : ∀ i, oriented n (v i) ≤ cap n (level i))
    (hcpos : ∀ j ≤ n, (univ.filter (fun i ↦ 0 ≤ v i ∧ level i = j)).card ≤ n.choose j * n ^ j)
    (hcneg : ∀ j ≤ n, (univ.filter (fun i ↦ v i < 0 ∧ level i = j)).card ≤ n.choose j * n ^ j) :
    (∑ i, v i ^ (2 * k)) - 1 ≤ (2 / (n : ℝ) - 1) ^ (2 * k) +
      2 * ∑ j ∈ Icc 1 n, ((n.choose j : ℝ) * (n : ℝ) ^ j) * cap n j ^ (2 * k) := by
  have hN : 0 < (n : ℝ) := by positivity
  have hp := class_sum_le (k := k) (univ.filter fun i ↦ 0 ≤ v i) level (fun i ↦ v i ^ (2 * k))
    1 zero_le_one (fun i _ ↦ hl i)
    (fun i hi h0 ↦ by
      have h := (mem_filter.mp hi).2
      have hb : v i ≤ 1 := by simpa [oriented, h, h0] using hcap i
      simpa using pow_le_pow_left₀ h hb (2 * k))
    (fun i hi _ ↦ by
      have h := (mem_filter.mp hi).2
      exact pow_le_pow_left₀ h (by simpa [oriented, h] using hcap i) _)
    (fun j hj ↦ by simpa only [filter_filter] using hcpos j hj)
  have hnegC : 0 ≤ (2 / (n : ℝ) - 1) ^ (2 * k) := by rw [pow_mul]; positivity
  have hm := class_sum_le (k := k) (univ.filter fun i ↦ v i < 0) level (fun i ↦ v i ^ (2 * k))
    ((2 / (n : ℝ) - 1) ^ (2 * k)) hnegC (fun i _ ↦ hl i)
    (fun i hi h0 ↦ by
      have h := (mem_filter.mp hi).2
      have hb : 2 / (n : ℝ) - v i ≤ 1 := by simpa [oriented, not_le.mpr h, h0] using hcap i
      rw [← (even_two_mul k).neg_pow (v i), ← neg_sub (1 : ℝ) (2 / n),
        (even_two_mul k).neg_pow (1 - 2 / (n : ℝ))]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _)
    (fun i hi _ ↦ by
      have h := (mem_filter.mp hi).2
      have hb : 2 / (n : ℝ) - v i ≤ cap n (level i) := by
        simpa [oriented, not_le.mpr h] using hcap i
      rw [← (even_two_mul k).neg_pow (v i)]
      exact pow_le_pow_left₀ (by linarith) (by linarith [div_nonneg zero_le_two hN.le]) _)
    (fun j hj ↦ by simpa only [filter_filter] using hcneg j hj)
  have hsplit := sum_filter_add_sum_filter_not univ (fun i ↦ 0 ≤ v i) (fun i ↦ v i ^ (2 * k))
  simp only [not_le] at hsplit
  linarith only [hp, hm, hsplit]

private theorem sign_term {n k : ℕ} (hn : 2 ≤ n) :
    (2 / (n : ℝ) - 1) ^ (2 * k) ≤ exp (-2 * (2 * (k : ℝ) / n - log n)) := by
  have hN : 0 < (n : ℝ) := by positivity
  have hN2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 ≤ 1 - 2 / (n : ℝ) := sub_nonneg.mpr ((div_le_one hN).mpr hN2)
  have hh : 1 - 2 / (n : ℝ) ≤ exp (-(2 / (n : ℝ))) := by linarith [add_one_le_exp (-(2 / (n : ℝ)))]
  calc
    _ = (1 - 2 / (n : ℝ)) ^ (2 * k) := by rw [← neg_sub (1 : ℝ) (2 / n), (even_two_mul k).neg_pow]
    _ ≤ exp (-(2 / (n : ℝ))) ^ (2 * k) := pow_le_pow_left₀ hpos hh _
    _ ≤ _ := by
      rw [← exp_nat_mul, exp_le_exp]; push_cast
      have hl : 0 ≤ log (n : ℝ) := log_nonneg (by linarith)
      calc
        _ = -2 * (2 * (k : ℝ) / n) := by ring
        _ ≤ _ := by linarith only [hl]

/-- **Cutoff bound from a spectral moment.** Let `2 ≤ n`. Let `v` be a finite family of real
numbers with a level in `[0,n]` for each index. Suppose that the value
or its sign twist is at most `cap n j` at level `j`, and that each sign class contains at most
`n.choose j * n ^ j` indices at that level (zero belongs to the nonnegative class).
If `L ≤ 2` and `L² ≤ ∑ᵢ vᵢ^(2k) - 1`, then `L ≤ 2 e³ n exp (-2k/n)`.
For the random-transposition walk `L` is twice total variation (Diaconis and Shahshahani,
1981, Theorem 1 and §3). -/
theorem cutoff_of_spectrum {ι : Type*} [Fintype ι] {n k : ℕ} (hn : 2 ≤ n)
    (v : ι → ℝ) (level : ι → ℕ) (hl : ∀ i, level i ≤ n)
    (hcap : ∀ i, oriented n (v i) ≤ cap n (level i))
    (hcpos : ∀ j ≤ n, (univ.filter (fun i ↦ 0 ≤ v i ∧ level i = j)).card ≤ n.choose j * n ^ j)
    (hcneg : ∀ j ≤ n, (univ.filter (fun i ↦ v i < 0 ∧ level i = j)).card ≤ n.choose j * n ^ j)
    (L : ℝ) (htrivial : L ≤ 2) (hL : L ^ 2 ≤ (∑ i, v i ^ (2 * k)) - 1) :
    L ≤ (2 * exp 3) * ((n : ℝ) * exp (-2 * (k : ℝ) / n)) := by
  let d := 2 * (k : ℝ) / n - log n
  have hN : 0 < (n : ℝ) := by positivity
  have heq : (2 * exp 3) * ((n : ℝ) * exp (-2 * (k : ℝ) / n)) = 2 * exp (3 - d) := by
    rw [show (n : ℝ) * exp (-2 * (k : ℝ) / n) = exp (-d) by
      conv_lhs => lhs; rw [← exp_log hN]
      rw [← exp_add]; congr 1; dsimp [d]; ring]
    rw [mul_assoc, ← exp_add]; rfl
  rw [heq]
  by_cases hd : 3 ≤ d
  · have hs := hL.trans (spectrum_sum_le hn v level hl hcap hcpos hcneg)
    have hJ := deficit_sum hn hd
    have hsign := sign_term (k := k) hn
    change _ ≤ exp (-2 * d) at hsign
    have hsign' := hsign.trans (exp_le_exp.mpr (show -2 * d ≤ -2 * (d - 3) by linarith))
    have hE : exp (-2 * (d - 3)) = exp (3 - d) ^ 2 := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    change _ ≤ exp (-2 * (d - 3)) at hJ
    rw [hE] at hJ hsign'
    nlinarith [exp_pos (3 - d), sq_nonneg (L + 2 * exp (3 - d))]
  · have he : 1 ≤ exp (3 - d) := one_le_exp_iff.mpr (by linarith)
    linarith

/-- For `0 < n`, the rate `n * exp (-2k/n)` is `exp (-2c)` for the cutoff parameter
`c = (k - n log n / 2) / n` of Diaconis and Shahshahani (1981, Theorem 1). -/
theorem cutoff_rate_eq {n k : ℕ} (hn : 0 < n) :
    (n : ℝ) * exp (-2 * (k : ℝ) / n) = exp (-2 * (((k : ℝ) - n * log n / 2) / n)) := by
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  conv_lhs => lhs; rw [← exp_log hN]
  rw [← exp_add]; congr 1; field_simp [hN.ne']; ring

end MathlibExt.Probability.RandomTranspositionEstimates
