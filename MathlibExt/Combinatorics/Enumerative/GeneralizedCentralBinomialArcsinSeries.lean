/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
public import MathlibExt.Combinatorics.Enumerative.GeneralizedCentralBinomialArcsin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal

/-!
# Zurita's reciprocal central binomial series

We expand the arcsine factor by Lehmer's series. A recurrence for the coefficients of its
product with `zuritaS` gives the tail of the desired series and identifies the initial terms
that must be subtracted.
-/

open Finset

namespace MetaMathlibExt

namespace ZuritaReciprocalSeries

private noncomputable def a (k : ℕ) : ℝ := 4 ^ k / Nat.centralBinom k

-- The coefficient of degree k + 1 in the arcsine factor.
private noncomputable def b (k : ℕ) : ℝ := a k / (2 * (k : ℝ) + 1)

private theorem a_zero : a 0 = 1 := by norm_num [a, Nat.centralBinom]

private theorem b_zero : b 0 = 1 := by simp [b, a_zero]

private theorem a_step (k : ℕ) :
    (2 * (k : ℝ) + 1) * a (k + 1) = 2 * ((k : ℝ) + 1) * a k := by
  have h := congrArg (fun m : ℕ => (m : ℝ)) (Nat.succ_mul_centralBinom_succ k)
  push_cast at h
  have h₁ : (Nat.centralBinom k : ℝ) ≠ 0 := by exact_mod_cast (Nat.centralBinom_pos k).ne'
  have h₂ : (Nat.centralBinom (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos (k + 1)).ne'
  unfold a
  rw [pow_succ]
  field_simp
  linear_combination -2 * h

private theorem b_mul (k : ℕ) : (2 * (k : ℝ) + 1) * b k = a k := by
  rw [b, mul_div_cancel₀ _ (by positivity)]

private theorem b_mul_succ (k : ℕ) : (2 * ((k : ℝ) + 1)) * b k = a (k + 1) := by
  have h : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  rw [b, ← mul_div_assoc, div_eq_iff h]
  linear_combination -(a_step k)

private theorem b_sub (k : ℕ) : b k = a (k + 1) - a k := by
  linear_combination b_mul_succ k - b_mul k

private theorem b_eq (k : ℕ) :
    b k = (4 : ℝ) ^ (k + 1) / (2 * (((k + 1 : ℕ) : ℝ) * Nat.centralBinom (k + 1))) := by
  have h := b_mul_succ k
  have hpos : (0 : ℝ) < Nat.centralBinom (k + 1) := by exact_mod_cast Nat.centralBinom_pos (k + 1)
  unfold a at h
  have hc := (eq_div_iff hpos.ne').1 h
  apply (eq_div_iff (by positivity)).2
  push_cast
  linear_combination hc

private theorem b_step (k : ℕ) : ((k : ℝ) + 1 + 1 / 2) * b (k + 1) = ((k : ℝ) + 1) * b k := by
  have h := b_mul (k + 1)
  push_cast at h
  linear_combination (h - b_mul_succ k) / 2

private noncomputable def sReal (n k : ℕ) : ℝ := zuritaSCoeff n k

private theorem s_zero (n : ℕ) : (1 / 2 - (n : ℝ)) * sReal n 0 = 1 := by
  have h : (1 / 2 - (n : ℝ)) ≠ 0 := by
    cases n with
    | zero => norm_num
    | succ n => push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [sReal, zuritaSCoeff]
  push_cast
  exact mul_one_div_cancel h

private theorem s_step (n k : ℕ) :
    ((k : ℝ) + 1 - n + 1 / 2) * sReal n (k + 1) = ((k : ℝ) - n) * sReal n k := by
  have h : (k : ℝ) + 1 - n + 1 / 2 ≠ 0 := by
    rcases le_or_gt n (k + 1) with hk | hk
    · have := (Nat.cast_le (α := ℝ)).mpr hk
      push_cast at this
      linarith
    · have := (Nat.cast_le (α := ℝ)).mpr (show k + 2 ≤ n by omega)
      push_cast at this
      linarith
  simp only [sReal, zuritaSCoeff, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
  rw [← mul_assoc, mul_div_cancel₀ _ h]

private theorem s_eq_zero_of_lt {n k : ℕ} (h : n < k) : sReal n k = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le (show n ≤ k by omega) with rfl | hk
    · simp [sReal, zuritaSCoeff]
    · have hrec := s_step n k
      rw [ih hk, mul_zero] at hrec
      have hkn : (n : ℝ) < k := by exact_mod_cast hk
      exact (mul_eq_zero.mp hrec).resolve_left (by linarith)

-- The recurrence for s telescopes when summed without the powers of x.
private theorem sum_s (n j : ℕ) :
    (∑ k ∈ range (j + 1), sReal n k / 2) = 1 - ((j : ℝ) - n) * sReal n j := by
  induction j with
  | zero => simp; linear_combination s_zero n
  | succ j ih =>
    rw [sum_range_succ, ih]
    push_cast
    linear_combination s_step n j

private theorem t_weight (m i k : ℕ) (hk : k + i = m) :
    ((k : ℝ) + 1 - (m + 2)) * (zuritaTCoeffRev (m + 2) i : ℝ) =
      ((k : ℝ) - (m + 2)) * sReal (m + 2) k - 1 := by
  induction i generalizing k with
  | zero =>
    have hk' : k = m := by omega
    subst k
    rw [zuritaTCoeffRev, zuritaC, show m + 2 - 1 = m + 1 by omega]
    push_cast
    rw [← sReal, ← sReal]
    have h₁ := s_step (m + 2) m
    have h₂ := s_step (m + 2) (m + 1)
    push_cast at h₁ h₂
    linear_combination h₂ + h₁
  | succ i ih =>
    have h := ih (k + 1) (by omega)
    have hs := s_step (m + 2) k
    rw [zuritaTCoeffRev, show m + 2 - 2 - i = k + 1 by omega]
    push_cast at h hs ⊢
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
    rw [mul_div_cancel₀ _ (by linarith)]
    change ((k : ℝ) + 1 + 1 - (↑m + 2)) * (zuritaTCoeffRev (m + 2) i : ℝ) +
      sReal (m + 2) (k + 1) / 2 = _
    linear_combination h + hs

-- The coefficient of degree j + 1 in the product of Sₙ with the arcsine factor.
private noncomputable def coeff (n j : ℕ) : ℝ :=
  ∑ k ∈ range (j + 1), sReal n k * b (j - k)

private theorem coeff_step (n j : ℕ) :
    ((j : ℝ) + 2 - n) * coeff n (j + 1) =
      ((j : ℝ) + 1 - n) * coeff n j + b (j + 1) + sReal n (j + 1) / 2 := by
  have hb (k : ℕ) (hk : k ∈ range (j + 1)) :
      ((j : ℝ) + 1 - k + 1 / 2) * b (j + 1 - k) = ((j : ℝ) + 1 - k) * b (j - k) := by
    have hkj : k ≤ j := by simpa [Nat.lt_succ_iff] using hk
    have heq : j + 1 - k = (j - k) + 1 := by omega
    rw [heq]
    have h := b_step (j - k)
    rw [Nat.cast_sub hkj] at h
    convert h using 1 <;> ring
  -- Split the weight into the weights from the b and s recurrences respectively.
  have hsplit : ((j : ℝ) + 2 - n) * coeff n (j + 1) =
      (∑ k ∈ range (j + 2), sReal n k * (((j : ℝ) + 1 - k + 1 / 2) * b (j + 1 - k))) +
      ∑ k ∈ range (j + 2), (((k : ℝ) - n + 1 / 2) * sReal n k) * b (j + 1 - k) := by
    rw [coeff, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hsplit, sum_range_succ (n := j + 1), sum_range_succ' (n := j + 1)]
  simp only [Nat.sub_self, b_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.sub_zero,
    zero_sub]
  have hsum :
      (∑ k ∈ range (j + 1), sReal n k * (((j : ℝ) + 1 - k + 1 / 2) * b (j + 1 - k))) +
        (∑ k ∈ range (j + 1), (((k : ℝ) + 1 - n + 1 / 2) * sReal n (k + 1)) *
          b (j + 1 - (k + 1))) = ((j : ℝ) + 1 - n) * coeff n j := by
    rw [coeff, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [hb k hk, s_step, Nat.add_sub_add_right]
    ring
  linear_combination hsum + b (j + 1) * s_zero n
private theorem coeff_weight (n j : ℕ) :
    ((j : ℝ) + 1 - n) * coeff n j = a (j + 1) - 1 + ∑ k ∈ range (j + 1), sReal n k / 2 := by
  induction j with
  | zero =>
    rw [coeff, sum_range_one, sum_range_one]
    simp only [Nat.cast_zero, zero_add, Nat.zero_sub, b_zero, mul_one]
    linear_combination s_zero n + b_sub 0 - b_zero - a_zero
  | succ j ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination coeff_step n j + ih + b_sub (j + 1)

-- Below degree n, T removes the part of the coefficient coming from S.
private theorem coeff_add_t (n j : ℕ) (hj : j + 1 < n) :
    coeff n j + (zuritaTCoeff n j : ℝ) = (a (j + 1) - 1) / ((j : ℝ) + 1 - n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have ht := t_weight m (m - j) j (by omega)
  have hc := coeff_weight (m + 2) j
  rw [sum_s] at hc
  have hlt : (j : ℝ) + 1 < ↑(m + 2 : ℕ) := by exact_mod_cast hj
  rw [eq_div_iff (by linarith : (j : ℝ) + 1 - ↑(m + 2 : ℕ) ≠ 0)]
  unfold zuritaTCoeff
  rw [Nat.add_sub_cancel]
  push_cast at hc ⊢
  linear_combination hc + ht

-- Above degree n, the full sum of s/2 is 1 and only the reciprocal binomial coefficient remains.
private theorem coeff_eq_of_le (n j : ℕ) (hj : n ≤ j) :
    coeff n j = a (j + 1) / ((j : ℝ) + 1 - n) := by
  have h := coeff_weight n j
  rw [sum_s] at h
  obtain rfl | hnj := eq_or_lt_of_le hj
  · simpa only [add_sub_cancel_left, div_one, one_mul, sub_self, zero_mul, sub_zero,
      sub_add_cancel] using h
  · rw [s_eq_zero_of_lt hnj, mul_zero, sub_zero, sub_add_cancel] at h
    have hle : (n : ℝ) ≤ j := by exact_mod_cast hj
    exact (eq_div_iff (by linarith)).2 ((mul_comm _ _).trans h)

private theorem coeff_at_degree (j : ℕ) :
    coeff (j + 1) j = 1 / 2 * ∑ k ∈ Icc 1 (j + 1),
      (4 : ℝ) ^ k * (zuritaSCoeff (j + 1) (j + 1 - k) : ℝ) /
        ((k : ℝ) * Nat.centralBinom k) := by
  rw [coeff, mul_sum]
  refine sum_bij (fun k _ => j - k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_range] at hk
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k hk l hl heq
    rw [mem_range] at hk hl
    omega
  · intro k hk
    obtain ⟨hk0, hk1⟩ := mem_Icc.mp hk
    refine ⟨j + 1 - k, mem_range.mpr (by omega), by omega⟩
  · intro k hk
    have hk' := mem_range.mp hk
    rw [show j + 1 - (j - k + 1) = k by omega, b_eq]
    unfold sReal
    ring

private theorem hasSum_b {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => b k * x ^ (k + 1))
      (Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x)) := by
  have hs : |Real.sqrt x| < 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
    nlinarith only [Real.sq_sqrt hx0.le, hx1]
  have h := (arcsin_central_binomial_reciprocal_series (Real.sqrt x) hs).mul_left (1 / 2)
  convert h using 1
  · ext k
    change b k * x ^ (k + 1) = 1 / 2 * _
    rw [b_eq, pow_mul, show (2 * Real.sqrt x) ^ 2 = 4 * x by
      rw [mul_pow, Real.sq_sqrt hx0.le]; norm_num, mul_pow]
    change (4 : ℝ) ^ (k + 1) / (2 * (((k + 1 : ℕ) : ℝ) * Nat.centralBinom (k + 1))) *
      x ^ (k + 1) = 1 / 2 * (4 ^ (k + 1) * x ^ (k + 1) /
        (((k + 1 : ℕ) : ℝ) * Nat.centralBinom (k + 1)))
    rw [div_mul_eq_mul_div, ← div_div]
    ring
  · rw [Real.sqrt_div hx0.le, Real.sq_sqrt hx0.le]
    ring

private theorem hasSum_coeff (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun j => coeff n j * x ^ (j + 1))
      (Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x) * zuritaS n x) := by
  have hs_zero (k : ℕ) (hk : k ∉ range (n + 1)) : sReal n k * x ^ k = 0 := by
    rw [s_eq_zero_of_lt (by simpa [mem_range, not_lt] using hk), zero_mul]
  have hs : HasSum (fun k => sReal n k * x ^ k) (zuritaS n x) :=
    hasSum_sum_of_ne_finset_zero hs_zero
  have hsn : Summable (fun k => ‖sReal n k * x ^ k‖) :=
    (hasSum_sum_of_ne_finset_zero (fun k hk => by rw [hs_zero k hk, norm_zero])).summable
  have hb := hasSum_b hx0 hx1
  have hbn : Summable (fun k => ‖b k * x ^ (k + 1)‖) := by
    convert hb.summable using 1
    ext k
    rw [Real.norm_eq_abs, abs_of_nonneg]
    unfold b a
    positivity
  have h := hasSum_sum_range_mul_of_summable_norm hsn hbn
  rw [hs.tsum_eq, hb.tsum_eq, mul_comm] at h
  convert h using 1
  ext j
  rw [coeff, sum_mul]
  apply sum_congr rfl
  intro k hk
  have hkj := mem_range.mp hk
  rw [show j + 1 = k + (j - k + 1) by omega, pow_add]
  ring

end ZuritaReciprocalSeries

open ZuritaReciprocalSeries

public section

/-- **Zurita's series $\sum_{k > n} 4^k x^k / ((k - n)\binom{2k}{k})$.** Let $n \ge 1$, let
$S_n(x) = \sum_{k=0}^n s_k x^k$ and $T_{n-2}$ be Zurita's polynomials (with $T_{-1} = 0$), and
let $x$ be real with $0 < x < 1$. Then
$$
\sum_{k > n} \frac{4^k x^k}{(k - n)\binom{2k}{k}} = x\, T_{n-2}(x) +
\sqrt{\frac{x}{1 - x}}\, \arcsin(\sqrt{x})\, S_n(x) +
\sum_{k=0}^{n-1} \Bigl(1 - \frac{4^k}{\binom{2k}{k}}\Bigr) \frac{x^k}{k - n} -
\Bigl(\frac12 \sum_{k=1}^{n} \frac{4^k s_{n-k}}{k \binom{2k}{k}}\Bigr) x^n.
$$

The source prints the range $|x| < 4$. The statement here is restricted to $0 < x < 1$, inside
the range $|x| < 1$ that the source's Theorem 1 gives in this case; since
$\binom{2k}{k} \le 4^k$, the series diverges for $x \ge 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 1 (`integers-2026-A2-cor-1`). -/
theorem tsum_four_pow_div_sub_mul_centralBinom {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) * Nat.centralBinom (k + n + 1)) =
      x * zuritaT n x + Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x) * zuritaS n x +
        ∑ k ∈ range n, (1 - (4 : ℝ) ^ k / Nat.centralBinom k) * x ^ k / ((k : ℝ) - n) -
        (1 / 2 * ∑ k ∈ Icc 1 n, (4 : ℝ) ^ k * (zuritaSCoeff n (n - k) : ℝ) /
          ((k : ℝ) * Nat.centralBinom k)) * x ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one]
  have hprod := hasSum_coeff (m + 1) hx0 hx1
  have hsplit := hprod.summable.sum_add_tsum_nat_add (m + 1)
  rw [hprod.tsum_eq, sum_range_succ, coeff_at_degree] at hsplit
  have htail : (∑' k : ℕ, coeff (m + 1) (k + (m + 1)) * x ^ (k + (m + 1) + 1)) =
      ∑' k : ℕ, (4 : ℝ) ^ (k + (m + 1) + 1) * x ^ (k + (m + 1) + 1) /
        (((k : ℝ) + 1) * Nat.centralBinom (k + (m + 1) + 1)) := by
    apply tsum_congr
    intro k
    rw [coeff_eq_of_le _ _ (by omega), a]
    push_cast
    rw [show (k : ℝ) + (↑m + 1) + 1 - (↑m + 1) = (k : ℝ) + 1 by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  rw [htail] at hsplit
  have hlow : x * zuritaT (m + 1) x + ∑ j ∈ range m, coeff (m + 1) j * x ^ (j + 1) =
      -(∑ k ∈ range (m + 1), (1 - a k) * x ^ k / ((k : ℝ) - ↑(m + 1 : ℕ))) := by
    change x * (∑ j ∈ range m, (zuritaTCoeff (m + 1) j : ℝ) * x ^ j) + _ = _
    rw [mul_sum, ← sum_add_distrib, sum_range_succ']
    simp only [a_zero, sub_self, zero_mul, zero_div, add_zero]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    rw [show x * (↑(zuritaTCoeff (m + 1) j) * x ^ j) + coeff (m + 1) j * x ^ (j + 1) =
      (coeff (m + 1) j + ↑(zuritaTCoeff (m + 1) j)) * x ^ (j + 1) by rw [pow_succ]; ring]
    rw [coeff_add_t _ _ (by have := mem_range.mp hj; omega)]
    push_cast
    ring
  unfold a at hlow
  linear_combination hsplit - hlow

end

end MetaMathlibExt
