/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Binomial power sums with harmonic differences

Expanding powers in falling factorials and differentiating the resulting binomial
convolution gives the Stirling expansion of an alternating binomial–harmonic sum.
-/

namespace MetaMathlibExt

open Finset

namespace sum_choose_sub_harmonic_diff_stirling

private theorem choose_reflect (z : ℂ) (k : ℕ) :
    Ring.choose z k = (-1 : ℂ) ^ k * Ring.choose (-z + k - 1) k := by
  simpa only [neg_neg, Units.smul_def, zsmul_eq_mul, Int.coe_negOnePow_natCast,
    Int.cast_pow, Int.cast_neg, Int.cast_one] using Ring.choose_neg (-z) k

-- The terms below j vanish. After shifting by j, the remaining sum is Chu–Vandermonde.
private theorem choose_convolution (z : ℂ) (j m : ℕ) :
    ∑ k ∈ range (j + m + 1), (-1 : ℂ) ^ k * Ring.choose z (j + m - k) * (k.choose j : ℂ) =
      (-1) ^ (j + m) * Ring.choose (((j + m : ℕ) : ℂ) - z) m := by
  calc
    _ = (-1 : ℂ) ^ j * Ring.choose (-((j : ℂ) + 1) + z) m := by
      rw [Nat.add_assoc j m 1, sum_range_add, sum_eq_zero (s := range j)
        (fun k hk => by simp [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]), zero_add,
        Ring.add_choose_eq m (Commute.all _ _), Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
      apply sum_congr rfl
      intro k _
      rw [choose_reflect (-((j : ℂ) + 1)) k,
        show -(-((j : ℂ) + 1)) + k - 1 = ((j + k : ℕ) : ℂ) by push_cast; ring,
        Ring.choose_natCast, ← Nat.choose_symm_add, pow_add, Nat.add_sub_add_left]
      ring
    _ = _ := by
      rw [choose_reflect (-((j : ℂ) + 1) + z) m, pow_add, mul_assoc]
      rw [show -(-((j : ℂ) + 1) + z) + m - 1 = ((j + m : ℕ) : ℂ) - z by push_cast; ring]

private theorem power_expansion (r n k : ℕ) (hk : k ≤ n) :
    (k : ℂ) ^ r = ∑ j ∈ range (min r n + 1),
      ((j.factorial : ℂ) * Nat.stirlingSecond r j) * (k.choose j : ℂ) := by
  have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k r
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, mul_left_comm (Nat.stirlingSecond _ _),
    ← mul_assoc] at h
  suffices k ^ r = ∑ j ∈ range (min r n + 1),
      j.factorial * Nat.stirlingSecond r j * k.choose j by exact_mod_cast this
  rw [h]
  symm
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_left r n)))
  intro j hj hmin
  simp only [mem_range] at hj hmin
  simp [Nat.choose_eq_zero_of_lt (show k < j by omega)]

private theorem power_convolution (n r : ℕ) (z : ℂ) :
    ∑ k ∈ range (n + 1), ((-1 : ℂ) ^ k * (k : ℂ) ^ r) * Ring.choose z (n - k) =
      (-1 : ℂ) ^ n * ∑ j ∈ range (min r n + 1),
        ((j.factorial : ℂ) * Nat.stirlingSecond r j) * Ring.choose (n - z) (n - j) := by
  calc
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (min r n + 1),
          ((j.factorial : ℂ) * Nat.stirlingSecond r j) *
            ((-1 : ℂ) ^ k * Ring.choose z (n - k) * (k.choose j : ℂ)) := by
      apply sum_congr rfl
      intro k hk
      rw [power_expansion r n k (Nat.le_of_lt_succ (mem_range.mp hk)), mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    _ = _ := by
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro j hj
      have hjn : j ≤ n := le_trans (Nat.le_of_lt_succ (mem_range.mp hj)) (min_le_right r n)
      have h := choose_convolution z j (n - j)
      rw [Nat.add_sub_of_le hjn] at h
      rw [← mul_sum, h]
      ring

-- The logarithmic derivative of the falling factorial telescopes by the digamma recurrence.
private theorem choose_hasDerivAt (k : ℕ) (t : ℂ) (ht : ∀ m : ℤ, t ≠ m) :
    HasDerivAt (fun z => Ring.choose z k)
      (Ring.choose t k * (Complex.digamma (t + 1) - Complex.digamma (t - k + 1))) t := by
  induction k with
  | zero => simpa [Ring.choose_zero_right] using (hasDerivAt_const t (1 : ℂ))
  | succ k ih =>
    have step (z : ℂ) :
        Ring.choose z (k + 1) = Ring.choose z k * (z - k) / ((k : ℂ) + 1) := by
      apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero k)).mpr
      simpa [nsmul_eq_mul, Nat.choose_succ_self_right, mul_comm] using
        Ring.choose_smul_choose z (Nat.le_succ k)
    have hp (m : ℕ) : t - k ≠ -(m : ℂ) := fun h =>
      ht ((k : ℤ) - m) (by push_cast; linear_combination h)
    have htk : t - k ≠ 0 := by simpa using hp 0
    simp_rw [step]
    apply ((ih.mul ((hasDerivAt_id' t).sub_const (k : ℂ))).div_const ((k : ℂ) + 1)).congr_deriv
    rw [Complex.digamma_apply_add_one _ hp, Nat.cast_succ,
      show t - ((k : ℂ) + 1) + 1 = t - k by ring]
    field_simp
    ring

end sum_choose_sub_harmonic_diff_stirling

open sum_choose_sub_harmonic_diff_stirling in
/-- **Power sums of $\binom{t}{n-k}(H_t - H_{t-n+k})$ in Stirling form.** Let $t$ be a complex
number that is not an integer. For complex $x$ write $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$,
and write $H_x = \psi(x+1) + \gamma$, where $\psi$ is the digamma function and $\gamma$ is the
Euler–Mascheroni constant (only differences $H_x - H_y = \psi(x+1) - \psi(y+1)$ occur below).
Let ${r \brace k}$ denote the Stirling numbers of the second kind. For all natural numbers $n$
and $r$ (with $0^0 = 1$),
$$\sum_{k=0}^{n} (-1)^k \binom{t}{n-k} k^r (H_t - H_{t-n+k}) =
(-1)^n \sum_{k=0}^{\min(r,n)} k! {r \brace k} \binom{n-t}{n-k} (H_{k-t} - H_{n-t}).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 5 (`integers-2026-A109-thm-5`). -/
public theorem sum_choose_sub_harmonic_diff_stirling (n r : ℕ) (t : ℂ)
    (ht : ∀ m : ℤ, t ≠ m) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * Ring.choose t (n - k) * (k : ℂ) ^ r *
          (Complex.digamma (t + 1) - Complex.digamma (t - n + k + 1)) =
      (-1) ^ n * ∑ k ∈ range (min r n + 1),
        (k.factorial : ℂ) * (Nat.stirlingSecond r k : ℂ) * Ring.choose ((n : ℂ) - t) (n - k) *
          (Complex.digamma (k - t + 1) - Complex.digamma (n - t + 1)) := by
  have left (k : ℕ) (hk : k ∈ range (n + 1)) :
      HasDerivAt (fun z : ℂ => ((-1 : ℂ) ^ k * (k : ℂ) ^ r) * Ring.choose z (n - k))
        ((-1 : ℂ) ^ k * Ring.choose t (n - k) * (k : ℂ) ^ r *
          (Complex.digamma (t + 1) - Complex.digamma (t - n + k + 1))) t := by
    apply ((choose_hasDerivAt (n - k) t ht).const_mul _).congr_deriv
    rw [Nat.cast_sub (Nat.le_of_lt_succ (mem_range.mp hk)), sub_sub_eq_add_sub]
    ring_nf
  have ht' (m : ℤ) : (n : ℂ) - t ≠ m := fun h =>
    ht ((n : ℤ) - m) (by push_cast; linear_combination -h)
  have right (k : ℕ) (hk : k ∈ range (min r n + 1)) :
      HasDerivAt (fun z : ℂ =>
          ((k.factorial : ℂ) * Nat.stirlingSecond r k) * Ring.choose (n - z) (n - k))
        ((k.factorial : ℂ) * Nat.stirlingSecond r k * Ring.choose ((n : ℂ) - t) (n - k) *
          (Complex.digamma (k - t + 1) - Complex.digamma (n - t + 1))) t := by
    have hkn := le_trans (Nat.le_of_lt_succ (mem_range.mp hk)) (min_le_right r n)
    have h := (choose_hasDerivAt (n - k) (n - t) ht').comp t
      ((hasDerivAt_id' t).const_sub (n : ℂ))
    apply (h.const_mul _).congr_deriv
    rw [Nat.cast_sub hkn, show (n : ℂ) - t - (n - k) = k - t by ring]
    ring
  have h := HasDerivAt.fun_sum left
  simp_rw [power_convolution] at h
  exact h.unique ((HasDerivAt.fun_sum right).const_mul _)

end MetaMathlibExt
