/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Module

/-!
# Euler product of a sieve of dimension `k`

A bounded discrepancy in the weighted prime sums yields two-sided bounds of order
`(log z) ^ (-k)` for the sieve Euler product.
-/

open Finset

namespace MetaMathlibExt

namespace calzado_sieve_euler_product_asymp

/-- Reindex a filtered sum over primes by shifting its indices by two. -/
private theorem sum_from_two {P : Set ℕ} [DecidablePred (· ∈ P)]
    (hP : ∀ i ∈ P, 2 ≤ i) (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ (range (n + 2)).filter (· ∈ P), f i) =
      ∑ j ∈ range n, (if j + 2 ∈ P then f (j + 2) else 0) := by
  have hzero : ∑ i ∈ range 2, (if i ∈ P then f i else 0) = 0 :=
    sum_eq_zero fun i hi ↦ ite_eq_right fun hip ↦ (hP i hip).not_gt (mem_range.mp hi)
  rw [sum_filter, Nat.add_comm n 2, sum_range_add, hzero, zero_add]
  simp only [Nat.add_comm 2]

/-- A decreasing nonnegative weight preserves a bound on partial sums. -/
private theorem abs_weighted_sum_le {g w : ℕ → ℝ} {D : ℝ}
    (hg : ∀ n, |∑ i ∈ range n, g i| ≤ D) (hw : Antitone w) (hw₀ : ∀ i, 0 ≤ w i)
    (n : ℕ) : |∑ i ∈ range n, w i * g i| ≤ D * w 0 := by
  have hparts := sum_range_by_parts w g n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hterm : ∀ i, |(w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j| ≤
      D * (w i - w (i + 1)) := by
    intro i
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ i))), neg_sub, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hg _) (sub_nonneg.mpr (hw (Nat.le_succ i)))
  calc
    _ ≤ |w (n - 1) * ∑ i ∈ range n, g i| +
        |∑ i ∈ range (n - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), g j| :=
      abs_sub _ _
    _ ≤ D * w (n - 1) + ∑ i ∈ range (n - 1), D * (w i - w (i + 1)) := by
      rw [abs_mul, abs_of_nonneg (hw₀ _), mul_comm D]
      exact add_le_add (mul_le_mul_of_nonneg_left (hg _) (hw₀ _))
        ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ hterm i))
    _ = D * w 0 := by
      rw [← mul_sum, sum_range_sub']
      ring

private theorem log_sub_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x ∧ Real.log y - Real.log x ≤ (y - x) / x := by
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hx.ne' hy.ne'] at h₁
  rw [Real.log_div hy.ne' hx.ne'] at h₂
  rw [sub_div, sub_div, div_self hy.ne', div_self hx.ne']
  exact ⟨by linarith, h₂⟩

/-- The error in the linear approximation to `-log (1 - x)`, for `0 ≤ x < 1`. -/
private theorem log_remainder_bounds {x : ℝ} (hx : x < 1) :
    0 ≤ -Real.log (1 - x) - x ∧ -Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx
  have hlo := Real.log_le_sub_one_of_pos hpos
  have hhi := Real.one_sub_inv_le_log_of_pos hpos
  refine ⟨by linarith, ?_⟩
  calc
    _ ≤ (1 - x)⁻¹ - 1 - x := by linarith
    _ = _ := by field_simp; ring

end calzado_sieve_euler_product_asymp

open calzado_sieve_euler_product_asymp in
/-- **Size of the Euler product of a sieve of dimension $k$.** Let $P$ be a set of primes, $k > 0$
a real number, and $\omega$ a real-valued function on the natural numbers with
$0 \le \omega(p) < p$ for $p \in P$. Suppose there is a constant $C_0$ with
$|\sum_{p \in P,\ t \le p < z} \omega(p) \log p / p - k \log(z/t)| \le C_0$ for all real $t$ and
$z$ with $2 \le t \le z$. Then there are constants $c > 0$ and $C > 0$ such that for every real
$z \ge 2$, $c / (\log z)^k \le \prod_{p \in P,\ p < z} (1 - \omega(p)/p) \le C / (\log z)^k$.

The constants depend on $\omega$ and $P$, not only on $k$.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 3
(`integers-2026-A117-lem-3`). -/
public theorem calzado_sieve_euler_product_asymp (P : Set ℕ)
    [DecidablePred (· ∈ P)] (ω : ℕ → ℝ) (k : ℝ) (hk : 0 < k)
    (hP : ∀ p ∈ P, p.Prime ∧ 0 ≤ ω p ∧ ω p < p)
    (hdim : ∃ C₀ : ℝ, ∀ t z : ℝ, 2 ≤ t → t ≤ z →
      |∑ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
          ω p * Real.log p / p - k * Real.log (z / t)| ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      c / Real.log z ^ k ≤
          ∏ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
            (1 - ω p / p) ∧
        ∏ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
            (1 - ω p / p) ≤ C / Real.log z ^ k := by
  obtain ⟨C₀, hdim⟩ := hdim
  -- Index the terms from 2, padding the sequence by zero off the sieve prime set.
  let x (i : ℕ) : ℝ := if i ∈ P then ω i / i else 0
  let L (i : ℕ) : ℝ := Real.log ((i + 2 : ℕ) : ℝ)
  let w (i : ℕ) : ℝ := (L i)⁻¹
  let a (i : ℕ) : ℝ := x (i + 2) * L i
  let b (i : ℕ) : ℝ := k * (L (i + 1) - L i)
  have hx (i : ℕ) : 0 ≤ x i ∧ x i < 1 := by
    by_cases hi : i ∈ P
    · have hi₀ : (0 : ℝ) < i := Nat.cast_pos.mpr (hP i hi).1.pos
      simpa only [x, ite_eq_left hi] using
        ⟨div_nonneg (hP i hi).2.1 hi₀.le, (div_lt_one hi₀).mpr (hP i hi).2.2⟩
    · simp [x, hi]
  have hL (i : ℕ) : 0 < L i := Real.log_pos (by exact_mod_cast (by omega : 1 < i + 2))
  have hL_mono : Monotone L := fun i j hij ↦
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 2)
  have hw : Antitone w := fun i j hij ↦ inv_anti₀ (hL i) (hL_mono hij)
  have hw₀ (i : ℕ) : 0 ≤ w i := (inv_pos.mpr (hL i)).le
  have hL_step (i : ℕ) : L (i + 1) - L i ≤ L 0 := by
    have h : ((i + 1 + 2 : ℕ) : ℝ) ≤ 2 * ((i + 2 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    have hL0 : L 0 = Real.log 2 := rfl
    unfold L
    rw [← hL0] at hlog
    change _ - _ ≤ L 0
    linarith
  have hf (z : ℝ) :
      (range ⌈z⌉₊).filter (fun i : ℕ ↦ i ∈ P ∧ (i : ℝ) < z) =
        (range ⌈z⌉₊).filter (· ∈ P) := by
    ext i
    simp only [mem_filter, mem_range, ← Nat.lt_ceil]
    tauto
  have hpartial (n : ℕ) : |∑ i ∈ range n, (a i - b i)| ≤ C₀ := by
    have h := hdim 2 ((n + 2 : ℕ) : ℝ) le_rfl (by exact_mod_cast (by omega : 2 ≤ n + 2))
    have heq :
        (range ⌈((n + 2 : ℕ) : ℝ)⌉₊).filter
            (fun i : ℕ ↦ i ∈ P ∧ 2 ≤ (i : ℝ) ∧ (i : ℝ) < ((n + 2 : ℕ) : ℝ)) =
          (range (n + 2)).filter (· ∈ P) := by
      ext i
      simp only [mem_filter, mem_range, Nat.ceil_natCast, Nat.cast_lt]
      exact ⟨fun hi ↦ ⟨hi.1, hi.2.1⟩,
        fun hi ↦ ⟨hi.1, hi.2, by exact_mod_cast (hP i hi.2).1.two_le, hi.1⟩⟩
    rw [heq, sum_from_two (fun i hi ↦ (hP i hi).1.two_le), Real.log_div
      (by positivity) (by norm_num)] at h
    have ha_eq : (∑ i ∈ range n, a i) =
        ∑ i ∈ range n, (if i + 2 ∈ P then
          ω (i + 2) * Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) else 0) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i + 2 ∈ P <;> simp [a, x, L, hi, div_mul_eq_mul_div]
    have hb_eq : (∑ i ∈ range n, b i) = k * (L n - L 0) := by
      dsimp only [b]
      rw [← mul_sum, sum_range_sub]
    rw [sum_sub_distrib, ha_eq, hb_eq]
    exact h
  have hC₀ : 0 ≤ C₀ := (abs_nonneg _).trans (hpartial 0)
  -- Compare the weighted sums with the increments of log and log log.
  have hweight (u : ℕ → ℝ) (hu : Antitone u) (hu₀ : ∀ i, 0 ≤ u i) (n : ℕ) :
      |(∑ i ∈ range n, u i * a i) - ∑ i ∈ range n, u i * b i| ≤ C₀ * u 0 := by
    simpa only [mul_sub, sum_sub_distrib] using
      abs_weighted_sum_le hpartial hu hu₀ n
  have hdiff (i : ℕ) :
      0 ≤ w i * b i - k * (Real.log (L (i + 1)) - Real.log (L i)) ∧
      w i * b i - k * (Real.log (L (i + 1)) - Real.log (L i)) ≤
        k * L 0 * (w i - w (i + 1)) := by
    have h := log_sub_bounds (hL i) (hL (i + 1))
    have h₁ := mul_le_mul_of_nonneg_left h.1 hk.le
    have h₂ := mul_le_mul_of_nonneg_left h.2 hk.le
    simp only [div_eq_mul_inv, ← show w i = (L i)⁻¹ from rfl,
      ← show w (i + 1) = (L (i + 1))⁻¹ from rfl] at h₁ h₂
    have h₃ := mul_le_mul_of_nonneg_right (hL_step i) (sub_nonneg.mpr (hw (Nat.le_succ i)))
    dsimp only [b]
    exact ⟨by nlinarith, by nlinarith [mul_le_mul_of_nonneg_left h₃ hk.le]⟩
  have hmodel (n : ℕ) :
      |(∑ i ∈ range n, w i * b i) - k * (Real.log (L n) - Real.log (L 0))| ≤ k := by
    have heq : (∑ i ∈ range n, (w i * b i - k * (Real.log (L (i + 1)) - Real.log (L i)))) =
        (∑ i ∈ range n, w i * b i) - k * (Real.log (L n) - Real.log (L 0)) := by
      rw [sum_sub_distrib, ← mul_sum, sum_range_sub (fun i ↦ Real.log (L i))]
    rw [← heq, abs_of_nonneg (sum_nonneg fun i _ ↦ (hdiff i).1)]
    calc
      _ ≤ ∑ i ∈ range n, k * L 0 * (w i - w (i + 1)) :=
        sum_le_sum fun i _ ↦ (hdiff i).2
      _ = k * L 0 * (w 0 - w n) := by rw [← mul_sum, sum_range_sub']
      _ ≤ k := by
        calc
          _ ≤ k * L 0 * w 0 := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hk.le (hL 0).le)
            linarith [hw₀ n]
          _ = k := by rw [mul_assoc, show L 0 * w 0 = 1 from mul_inv_cancel₀ (hL 0).ne', mul_one]
  have ha (i : ℕ) : w i * a i = x (i + 2) := by
    dsimp [w, a]
    field_simp [(hL i).ne']
  have hlinear (n : ℕ) :
      |(∑ i ∈ range n, x (i + 2)) - k * (Real.log (L n) - Real.log (L 0))| ≤
        C₀ * w 0 + k := by
    have h := (abs_sub_le (∑ i ∈ range n, w i * a i) (∑ i ∈ range n, w i * b i)
      (k * (Real.log (L n) - Real.log (L 0)))).trans
        (add_le_add (hweight w hw hw₀ n) (hmodel n))
    simpa only [ha] using h
  -- The squared local densities have uniformly bounded partial sums.
  let D := 2 * C₀ + k * L 0
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ha_le (i : ℕ) : a i ≤ D := by
    have hi := (abs_le.mp (hpartial i)).1
    have hj := (abs_le.mp (hpartial (i + 1))).2
    rw [sum_range_succ] at hj
    dsimp only [D, b] at *
    linarith [mul_le_mul_of_nonneg_left (hL_step i) hk.le]
  let u (i : ℕ) := w i ^ 2
  have hu : Antitone u := fun i j hij ↦ (sq_le_sq₀ (hw₀ j) (hw₀ i)).mpr (hw hij)
  have hu₀ (i : ℕ) : 0 ≤ u i := sq_nonneg _
  have hmodel₂ (i : ℕ) : u i * b i ≤ 2 * k * (w i - w (i + 1)) := by
    have hj : L (i + 1) ≤ 2 * L i := by linarith [hL_step i, hL_mono (Nat.zero_le i)]
    have hΔ : 0 ≤ L (i + 1) - L i := sub_nonneg.mpr (hL_mono (Nat.le_succ i))
    dsimp [u, b, w]
    field_simp [(hL i).ne', (hL (i + 1)).ne']
    apply (div_le_div_iff₀ (pow_pos (hL i) _) (mul_pos (hL i) (hL (i + 1)))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hj (mul_nonneg hΔ (hL i).le)]
  let M := D * (C₀ * u 0 + 2 * k * w 0)
  have hsquare (n : ℕ) : ∑ i ∈ range n, x (i + 2) ^ 2 ≤ M := by
    have hb : ∑ i ∈ range n, u i * b i ≤ 2 * k * w 0 := by
      calc
        _ ≤ ∑ i ∈ range n, 2 * k * (w i - w (i + 1)) :=
          sum_le_sum fun i _ ↦ hmodel₂ i
        _ = 2 * k * (w 0 - w n) := by rw [← mul_sum, sum_range_sub']
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hk.le)
          linarith [hw₀ n]
    have h := (le_abs_self _).trans (hweight u hu hu₀ n)
    calc
      _ ≤ ∑ i ∈ range n, D * (u i * a i) := by
        apply sum_le_sum
        intro i _
        have hai : 0 ≤ a i := mul_nonneg (hx _).1 (hL i).le
        rw [← ha i]
        dsimp only [u]
        nlinarith [mul_le_mul_of_nonneg_left (ha_le i)
          (mul_nonneg (sq_nonneg (w i)) hai)]
      _ = D * ∑ i ∈ range n, u i * a i := (mul_sum ..).symm
      _ ≤ M := mul_le_mul_of_nonneg_left (by linarith) hD
  -- At large primes the logarithmic remainder is at most twice the square.
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (2 * D))
  let r (i : ℕ) := -Real.log (1 - x (i + 2)) - x (i + 2)
  have hr₀ (i : ℕ) : 0 ≤ r i := (log_remainder_bounds (hx _).2).1
  have hr (i : ℕ) (hi : N ≤ i) : r i ≤ 2 * x (i + 2) ^ 2 := by
    have hLlarge : 2 * D < L i := by
      apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
      exact hN.trans_le (by exact_mod_cast (by omega : N ≤ i + 2))
    have hxsmall : x (i + 2) ≤ 1 / 2 := by
      have h := ha_le i
      dsimp only [a] at h
      apply (le_div_iff₀ (hL i)).mpr at h
      exact h.trans ((div_le_iff₀ (hL i)).mpr (by linarith))
    exact (log_remainder_bounds (hx _).2).2.trans
      ((div_le_iff₀ (sub_pos.mpr (hx _).2)).mpr (by
        nlinarith [mul_nonneg (sq_nonneg (x (i + 2))) (show 0 ≤ 1 - 2 * x (i + 2) by linarith)]))
  let R := (∑ i ∈ range N, r i) + 2 * M
  have hrem (n : ℕ) : 0 ≤ ∑ i ∈ range n, r i ∧ ∑ i ∈ range n, r i ≤ R := by
    refine ⟨sum_nonneg fun i _ ↦ hr₀ i, ?_⟩
    calc
      _ ≤ ∑ i ∈ range n, ((if i < N then r i else 0) + 2 * x (i + 2) ^ 2) := by
        apply sum_le_sum
        intro i _
        split_ifs with hi
        · linarith [sq_nonneg (x (i + 2))]
        · simpa using hr i (Nat.le_of_not_gt hi)
      _ ≤ R := by
        rw [sum_add_distrib, ← sum_filter, ← mul_sum]
        exact add_le_add (sum_le_sum_of_subset_of_nonneg
          (fun i hi ↦ mem_range.mpr (mem_filter.mp hi).2) (fun i _ _ ↦ hr₀ i))
          (mul_le_mul_of_nonneg_left (hsquare n) (by norm_num))
  -- Round the real cutoff up to the integer indexing the partial sums.
  let B := C₀ * w 0 + k + R + k * L 0 + |k * Real.log (L 0)|
  refine ⟨Real.exp (-B), Real.exp B, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro z hz
  let n := ⌈z⌉₊ - 2
  have hzceil : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
  have hn : n + 2 = ⌈z⌉₊ := Nat.sub_add_cancel (by exact_mod_cast hz.trans hzceil)
  have hzlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hLn : L n = Real.log (⌈z⌉₊ : ℝ) := by simp only [L, hn]
  have hzL : Real.log z ≤ L n ∧ L n ≤ 2 * Real.log z := by
    rw [hLn]
    refine ⟨Real.log_le_log (by positivity) hzceil, ?_⟩
    have hceil : (⌈z⌉₊ : ℝ) ≤ z ^ 2 := by
      nlinarith [Nat.ceil_lt_add_one (show 0 ≤ z by linarith),
        mul_nonneg (show 0 ≤ z - 2 by linarith) (show 0 ≤ z + 1 by linarith)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) hceil
  have hlogz : 0 ≤ Real.log (L n) - Real.log (Real.log z) ∧
      Real.log (L n) - Real.log (Real.log z) ≤ L 0 := by
    have hlo := Real.log_le_log hzlog hzL.1
    have hhi := Real.log_le_log (hL n) hzL.2
    rw [Real.log_mul (by norm_num) hzlog.ne'] at hhi
    change _ ∧ _ ≤ Real.log 2
    exact ⟨by linarith, by linarith⟩
  -- Take logarithms of the finite product using positivity of the factors.
  let s := (range ⌈z⌉₊).filter (fun p : ℕ ↦ p ∈ P ∧ (p : ℝ) < z)
  let V := ∏ p ∈ s, (1 - ω p / p)
  have hfactor (p : ℕ) (hp : p ∈ s) : 0 < 1 - ω p / p := by
    have hpP := (mem_filter.mp hp).2.1
    simpa only [x, ite_eq_left hpP] using sub_pos.mpr (hx p).2
  have hV : 0 < V := prod_pos hfactor
  have hlogV : -Real.log V = ∑ i ∈ range n, (r i + x (i + 2)) := by
    have hs : s = (range ⌈z⌉₊).filter (· ∈ P) := hf z
    unfold V
    rw [Real.log_prod (fun p hp ↦ (hfactor p hp).ne'), ← sum_neg_distrib, hs, ← hn,
      sum_from_two (fun i hi ↦ (hP i hi).1.two_le)]
    apply sum_congr rfl
    intro i _
    by_cases hi : i + 2 ∈ P <;> simp [r, x, hi]
  have hre := hrem n
  have hlin := abs_le.mp (hlinear n)
  have hround := mul_le_mul_of_nonneg_left hlogz.2 hk.le
  have hround₀ := mul_nonneg hk.le hlogz.1
  have hnorm : -B ≤ Real.log V + k * Real.log (Real.log z) ∧
      Real.log V + k * Real.log (Real.log z) ≤ B := by
    rw [sum_add_distrib] at hlogV
    dsimp only [B]
    have hc := le_abs_self (k * Real.log (L 0))
    have hc' := neg_le_abs (k * Real.log (L 0))
    constructor <;> linarith
  have hpow : 0 < Real.log z ^ k := Real.rpow_pos_of_pos hzlog _
  have hlognorm : Real.log (V * Real.log z ^ k) = Real.log V + k * Real.log (Real.log z) := by
    rw [Real.log_mul hV.ne' hpow.ne', Real.log_rpow hzlog]
  rw [← hlognorm] at hnorm
  -- Exponentiate the two bounds and divide by the positive normalizing factor.
  have hlo := Real.exp_le_exp.mpr hnorm.1
  have hhi := Real.exp_le_exp.mpr hnorm.2
  rw [Real.exp_log (mul_pos hV hpow)] at hlo hhi
  exact ⟨(div_le_iff₀ hpow).mpr hlo, (le_div_iff₀ hpow).mpr hhi⟩

end MetaMathlibExt
