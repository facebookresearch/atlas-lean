/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
public import MathlibExt.Combinatorics.Enumerative.GeneralizedCentralBinomialArcsin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.RingTheory.PowerSeries.Derivative
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal

/-!
# Zurita's reciprocal central binomial series

For integers $n \ge 1$ and real $0 < x < 1$, we evaluate the tails with one and two
powers of $k-n$ in the denominator. For the first power, a recurrence for the product
of Lehmer's series with $S_n$ identifies the initial terms to subtract. For the square,
we apply the formal Euler operator $X\,d/dX-n$ to the arcsine terms and reuse the
coefficients from the first-power proof. Since this operator kills the term of degree
$n$, we compute that coefficient separately. The square-weighted identity is the
positive-real specialization of the source's formula on $|x| < 1$.

## References

- Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
  Coefficients*, INTEGERS 26 (2026), Article A2, pp. 1–21, Corollaries 1 and 2, Remarks 1
  and 3, and Lemmas 2 and 3.
- D. H. Lehmer, *Interesting Series Involving the Central Binomial Coefficient*, American
  Mathematical Monthly 92 (1985), pp. 449–457, for the arcsine series used in Lemma 3
  of Zurita's paper; see `arcsin_central_binomial_reciprocal_series`.
- Renzo Sprugnoli, *Sums of Reciprocals of the Central Binomial Coefficients*, INTEGERS 6
  (2006), Article A27, pp. 1–18, Theorem 2.3, for the arcsine-square series used in the
  proof of Zurita's Theorem 2.
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

namespace ZuritaSquaredSeries

open PowerSeries

private noncomputable def euler : Derivation ℝ ℝ⟦X⟧ ℝ⟦X⟧ :=
  (X : ℝ⟦X⟧) • PowerSeries.derivative

private theorem euler_apply (f : ℝ⟦X⟧) : euler f = X * PowerSeries.derivative f := rfl

private theorem coeff_euler (k : ℕ) (f : ℝ⟦X⟧) :
    PowerSeries.coeff k (euler f) = (k : ℝ) * PowerSeries.coeff k f := by
  rw [euler_apply]
  cases k with
  | zero => simp
  | succ k => rw [coeff_succ_X_mul, coeff_derivative, mul_comm]; simp

-- The normalized Euler operator multiplies the coefficient of degree k by k − n.
private noncomputable def weight (n : ℕ) : ℝ⟦X⟧ →ₗ[ℝ] ℝ⟦X⟧ :=
  euler.toLinearMap - (n : ℝ) • LinearMap.id

private theorem weight_apply (n : ℕ) (f : ℝ⟦X⟧) :
    weight n f = euler f - C (n : ℝ) * f := by
  simp [weight, smul_eq_C_mul]

private theorem coeff_weighted (n k : ℕ) (f : ℝ⟦X⟧) :
    PowerSeries.coeff k (weight n f) = ((k : ℝ) - n) * PowerSeries.coeff k f := by
  rw [weight_apply, map_sub, coeff_euler, coeff_C_mul, sub_mul]

private theorem weight_shift (n l : ℕ) (hl : l ≤ n) (s : ℝ) (f : ℝ⟦X⟧) :
    weight n (C s * (X ^ l * f)) = C s * (X ^ l * weight (n - l) f) := by
  ext k
  rw [coeff_weighted]
  simp only [coeff_C_mul, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_weighted, Nat.cast_sub h, Nat.cast_sub hl]
    ring
  · ring

private noncomputable def L : ℝ⟦X⟧ := X * PowerSeries.mk b

private noncomputable def A : ℝ⟦X⟧ :=
  X * PowerSeries.mk (fun k => b k / ((k : ℝ) + 1))

private noncomputable def P : ℝ⟦X⟧ := (1 - X) * L

private noncomputable def M (d : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk (fun k => if k < d then (zuritaMCoeff d k : ℝ) else 0)

private theorem coeff_L_succ (k : ℕ) : PowerSeries.coeff (k + 1) L = b k := by
  simp [L, coeff_succ_X_mul]

private theorem coeff_A_succ (k : ℕ) : PowerSeries.coeff (k + 1) A = b k / ((k : ℝ) + 1) := by
  simp [A, coeff_succ_X_mul]

private theorem coeff_M (d k : ℕ) :
    PowerSeries.coeff k (M d) = if k < d then (zuritaMCoeff d k : ℝ) else 0 := by
  simp [M]

private theorem euler_A : euler A = L := by
  ext k
  cases k with
  | zero => simp [L, coeff_euler]
  | succ k =>
    rw [coeff_euler, coeff_A_succ, coeff_L_succ, Nat.cast_succ, mul_div_cancel₀ _ (by positivity)]

private theorem euler_L : 2 * (euler L - X * euler L) - L = X := by
  ext k
  simp only [map_sub, coeff_ofNat_mul, coeff_euler, coeff_X]
  cases k with
  | zero => simp [L]
  | succ k =>
    rw [coeff_succ_X_mul, coeff_euler, coeff_L_succ]
    cases k with
    | zero => norm_num [L, b_zero]
    | succ k =>
      rw [ite_eq_right (show k + 1 + 1 ≠ 1 by omega), coeff_L_succ]
      push_cast
      linear_combination 2 * b_step k

private theorem euler_M (d : ℕ) (hd : 0 < d) :
    C ((d : ℝ) - 1 / 2) * M d - euler (M d) + X * weight (d - 1) (M d) = 1 := by
  ext k
  rw [map_add, map_sub, coeff_C_mul, coeff_euler]
  cases k with
  | zero =>
    rw [coeff_zero_X_mul, coeff_M, ite_eq_left hd, coeff_one]
    simpa only [Nat.cast_zero, sub_zero, zero_mul, add_zero, ite_true] using
      zuritaMCoeff_recurrence d 0
  | succ k =>
    rw [coeff_succ_X_mul, coeff_weighted, coeff_M, coeff_M, coeff_one,
      ite_eq_right (Nat.succ_ne_zero k)]
    rw [Nat.cast_sub hd, Nat.cast_one, Nat.cast_succ]
    by_cases h : k + 1 < d
    · rw [ite_eq_left h, ite_eq_left (show k < d by omega)]
      have hm := zuritaMCoeff_recurrence d (k + 1)
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, Nat.cast_succ] at hm
      linear_combination hm
    · rw [ite_eq_right h]
      by_cases h' : k < d
      · rw [ite_eq_left h', show d = k + 1 by omega, Nat.cast_succ]
        ring
      · rw [ite_eq_right h']
        ring

-- This is the coefficient form of the antiderivative identity for the M factor.
private theorem weight_neg_PM (d : ℕ) (hd : 0 < d) :
    weight d (-(P * M d)) = L - C (1 / 2) * (X * M d) := by
  have hL := congrArg (fun f : ℝ⟦X⟧ => C (1 / 2) * f * M d) euler_L
  have hM := congrArg (fun f : ℝ⟦X⟧ => L * f) (euler_M d hd)
  have hd' : (↑(d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  rw [weight_apply, hd'] at hM
  simp only [map_sub, map_one, mul_one] at hM
  have hhalf : C (1 / 2 : ℝ) * 2 = (1 : ℝ⟦X⟧) := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  rw [mul_sub, ← mul_assoc (C (1 / 2) : ℝ⟦X⟧) 2, hhalf, one_mul] at hL
  rw [weight_apply, map_neg, P, Derivation.leibniz, Derivation.leibniz, map_sub,
    Derivation.map_one_eq_zero, euler_apply X, derivative_X, mul_one]
  simp only [smul_eq_mul]
  linear_combination hM - hL

private noncomputable def K (n : ℕ) : ℝ⟦X⟧ :=
  ∑ l ∈ range n, C (sReal n l) * (X ^ l * M (n - l))

private noncomputable def F (n : ℕ) : ℝ⟦X⟧ := C (sReal n n) * (X ^ n * A) - P * K n

private theorem weight_F (n : ℕ) :
    weight n (F n) = L * PowerSeries.mk (sReal n) - C (1 / 2) * (X * K n) := by
  have hS : PowerSeries.mk (sReal n) = ∑ l ∈ range (n + 1), C (sReal n l) * X ^ l := by
    ext k
    simp only [coeff_mk, map_sum, coeff_C_mul_X_pow, sum_ite_eq, mem_range]
    split_ifs with hk
    · rfl
    · exact s_eq_zero_of_lt (by omega)
  have hP : -(P * K n) = ∑ l ∈ range n, C (sReal n l) * (X ^ l * -(P * M (n - l))) := by
    rw [K, mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro l _
    ring
  rw [F, sub_eq_add_neg, hP, map_add, map_sum, weight_shift n n le_rfl, Nat.sub_self]
  simp only [weight_apply 0, Nat.cast_zero, map_zero, zero_mul, sub_zero, euler_A]
  rw [hS, sum_range_succ, mul_add, K, mul_sum, mul_sum, mul_sum]
  rw [add_comm (∑ _ ∈ _, _) _, add_sub_assoc, ← sum_sub_distrib]
  congr 1
  · ring
  · apply sum_congr rfl
    intro l hl
    have hl' := mem_range.mp hl
    rw [weight_shift n l hl'.le, weight_neg_PM _ (by omega)]
    ring

private theorem coeff_LS (n j : ℕ) :
    PowerSeries.coeff (j + 1) (L * PowerSeries.mk (sReal n)) =
      ZuritaReciprocalSeries.coeff n j := by
  rw [L, mul_assoc, coeff_succ_X_mul, mul_comm, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ZuritaReciprocalSeries.coeff]
  simp only [coeff_mk]

private theorem coeff_K_below (n j : ℕ) (hj : j < n) :
    PowerSeries.coeff j (K n) =
      ∑ l ∈ range (j + 1), sReal n l * (zuritaMCoeff (n - l) (j - l) : ℝ) := by
  simp only [K, map_sum, coeff_C_mul, coeff_X_pow_mul']
  rw [← sum_subset (show range (j + 1) ⊆ range n from range_mono (by omega))]
  · apply sum_congr rfl
    intro l hl
    have hl' := mem_range.mp hl
    rw [ite_eq_left (by omega), coeff_M, ite_eq_left (by omega)]
  · intro l _ hl
    rw [ite_eq_right (by simpa only [mem_range, Nat.lt_succ_iff] using hl), mul_zero]

private theorem coeff_K_above (n j : ℕ) (hj : n ≤ j) : PowerSeries.coeff j (K n) = 0 := by
  simp only [K, map_sum, coeff_C_mul, coeff_X_pow_mul']
  apply sum_eq_zero
  intro l hl
  have hl' := mem_range.mp hl
  rw [ite_eq_left (by omega), coeff_M, ite_eq_right (by omega), mul_zero]

private theorem coeff_F_zero (n : ℕ) : PowerSeries.coeff 0 (F n) = 0 := by
  rw [F, map_sub, coeff_C_mul, coeff_X_pow_mul', P, sub_mul, one_mul, sub_mul, map_sub]
  simp [A, L, mul_assoc]

-- The printed polynomials use degrees k, rather than the successor index of b and coeff.
private noncomputable def rCoeff (n k : ℕ) : ℝ :=
  (zuritaTCoeff n (k - 1) : ℝ) / ((k : ℝ) - n) +
    1 / 2 * (∑ l ∈ range k, sReal n l * (zuritaMCoeff (n - l) (k - l - 1) : ℝ) /
      ((k : ℝ) - n)) + (1 - a k) / ((k : ℝ) - n) ^ 2

private theorem coeff_F_below (n j : ℕ) (hj : j + 1 < n) :
    PowerSeries.coeff (j + 1) (F n) = -rCoeff n (j + 1) := by
  have h := congrArg (PowerSeries.coeff (j + 1)) (weight_F n)
  rw [coeff_weighted, map_sub, coeff_LS, coeff_C_mul, coeff_succ_X_mul,
    coeff_K_below _ _ (by omega)] at h
  have ht := coeff_add_t n j hj
  have hj' : (j : ℝ) + 1 < n := by exact_mod_cast hj
  have hne : (j : ℝ) + 1 - n ≠ 0 := by linarith
  have hsum (l : ℕ) (hl : l ∈ range (j + 1)) : j + 1 - l - 1 = j - l := by
    have := mem_range.mp hl
    omega
  simp only [rCoeff, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← Finset.sum_div] at h ⊢
  rw [sum_congr rfl (fun l hl => by rw [hsum l hl])]
  field_simp [hne] at ht ⊢
  linear_combination 2 * (((j : ℝ) + 1 - n) * h + ht)

private theorem coeff_F_above (n j : ℕ) (hj : n ≤ j) :
    PowerSeries.coeff (j + 1) (F n) = a (j + 1) / ((j : ℝ) + 1 - n) ^ 2 := by
  have h := congrArg (PowerSeries.coeff (j + 1)) (weight_F n)
  rw [coeff_weighted, map_sub, coeff_LS, coeff_C_mul, coeff_succ_X_mul,
    coeff_K_above _ _ hj, mul_zero, sub_zero, coeff_eq_of_le _ _ hj] at h
  have hj' : (n : ℝ) ≤ j := by exact_mod_cast hj
  have hne : (j : ℝ) + 1 - n ≠ 0 := by linarith
  push_cast at h
  field_simp [hne] at h ⊢
  linear_combination h

private theorem s_last (n : ℕ) (hn : 0 < n) : sReal n n = 2 * a n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := coeff_weight (m + 1) m
  have hs := sum_s (m + 1) (m + 1)
  rw [sum_range_succ] at hs
  simp only [Nat.succ_eq_add_one] at h hs ⊢
  push_cast at h hs
  linear_combination 2 * (hs + h)

private theorem m_last (d : ℕ) (hd : 0 < d) :
    (zuritaMCoeff d (d - 1) : ℝ) = a d / (d : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have h := congrArg (PowerSeries.coeff (m + 1)) (weight_neg_PM (m + 1) hd)
  rw [coeff_weighted, map_sub, coeff_L_succ, coeff_C_mul, coeff_succ_X_mul,
    coeff_M, ite_eq_left (Nat.lt_succ_self m)] at h
  have hb := b_mul_succ m
  simp only [Nat.succ_sub_one, Nat.cast_succ] at h ⊢
  apply (eq_div_iff (by positivity)).2
  linear_combination 2 * ((m : ℝ) + 1) * h + hb

private theorem coeff_P_one : PowerSeries.coeff 1 P = 1 := by
  rw [P, sub_mul, one_mul, map_sub, coeff_L_succ 0, coeff_succ_X_mul 0, b_zero]
  simp [L]

private theorem coeff_P_succ (p : ℕ) (hp : 0 < p) :
    PowerSeries.coeff (p + 1) P = -b p / (2 * (p : ℝ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [P, sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_L_succ, coeff_L_succ,
    Nat.cast_succ]
  apply (eq_div_iff (by positivity)).2
  linear_combination 2 * b_step j

private theorem coeff_PM_diag (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff d (P * M d) = a d / (d : ℝ) -
      1 / 2 * ∑ p ∈ Icc 1 (d - 1), b p * (zuritaMCoeff d (d - 1 - p) : ℝ) / (p : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.succ_eq_add_one, sum_range_succ', sum_range_succ']
  simp only [Nat.succ_eq_add_one, Nat.sub_zero, coeff_M, lt_self_iff_false, ite_false, mul_zero,
    add_zero, Nat.zero_add, Nat.add_sub_cancel, Nat.add_sub_add_right, coeff_P_one,
    Nat.lt_succ_self, ite_true, one_mul]
  have hm := m_last (m + 1) hd
  rw [Nat.add_sub_cancel] at hm
  rw [hm]
  have hsum : (∑ p ∈ range m, PowerSeries.coeff (p + 1 + 1) P *
        (if m - (p + 1) < m + 1 then (zuritaMCoeff (m + 1) (m - (p + 1)) : ℝ) else 0)) =
      ∑ p ∈ Icc 1 m, -(1 / 2) * (b p * (zuritaMCoeff (m + 1) (m - p) : ℝ) / (p : ℝ)) := by
    refine sum_bij (fun p _ => p + 1) ?_ ?_ ?_ ?_
    · intro p hp
      exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hp; omega⟩
    · intro i _ j _ h
      omega
    · intro p hp
      obtain ⟨hp1, hpm⟩ := mem_Icc.mp hp
      exact ⟨p - 1, mem_range.mpr (by omega), by omega⟩
    · intro p _
      rw [ite_eq_left (by omega), coeff_P_succ (p + 1) (by omega)]
      ring
  rw [hsum, ← mul_sum]
  ring

private noncomputable def qCoeff (n : ℕ) : ℝ :=
  -(2 * a n) + ∑ l ∈ range (n - 1), sReal n l *
    (a (n - l) / (↑(n - l : ℕ) : ℝ) -
      1 / 2 * ∑ p ∈ Icc 1 (n - l - 1),
        b p * (zuritaMCoeff (n - l) (n - l - 1 - p) : ℝ) / (p : ℝ))

private theorem coeff_F_diag (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (F n) = -qCoeff n := by
  rw [F, map_sub, coeff_C_mul, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
    show PowerSeries.coeff 0 A = 0 by simp [A], mul_zero, zero_sub, K, mul_sum, map_sum]
  apply congrArg Neg.neg
  have hcoeff (l : ℕ) (hl : l ∈ range n) :
      PowerSeries.coeff n (P * (C (sReal n l) * (X ^ l * M (n - l)))) =
        sReal n l * (a (n - l) / (↑(n - l : ℕ) : ℝ) -
          1 / 2 * ∑ p ∈ Icc 1 (n - l - 1),
            b p * (zuritaMCoeff (n - l) (n - l - 1 - p) : ℝ) / (p : ℝ)) := by
    have hl' := mem_range.mp hl
    rw [show P * (C (sReal n l) * (X ^ l * M (n - l))) =
        C (sReal n l) * (X ^ l * (P * M (n - l))) by ring,
      coeff_C_mul, coeff_X_pow_mul', ite_eq_left hl'.le, coeff_PM_diag _ (by omega)]
  rw [sum_congr rfl hcoeff]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [qCoeff, Nat.succ_sub_one, sum_range_succ]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, Nat.cast_one, div_one, Nat.sub_self,
    Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 0), sum_empty, mul_zero, sub_zero]
  have hs := s_step (m + 1) m
  have hlast := s_last (m + 1) hn
  have ha : a 1 = 2 := by simpa only [b_zero, Nat.cast_zero, zero_add, mul_one] using
    (b_mul_succ 0).symm
  push_cast at hs
  linear_combination 2 * hs - hlast + sReal (m + 1) m * ha

-- Evaluate only the series shown to converge, rather than assigning a real value to every series.
private def Evaluates (f : ℝ⟦X⟧) (x y : ℝ) : Prop :=
  HasSum (fun k => PowerSeries.coeff k f * x ^ k) y

private theorem eval_shift {f : ℝ⟦X⟧} {x y : ℝ} (h : Evaluates f x y) (s : ℝ) (l : ℕ) :
    Evaluates (C s * (X ^ l * f)) x (s * (x ^ l * y)) := by
  have hz : (∑ k ∈ range l, PowerSeries.coeff k (C s * (X ^ l * f)) * x ^ k) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [coeff_C_mul, coeff_X_pow_mul', ite_eq_right (not_le_of_gt (mem_range.mp hk)),
      mul_zero, zero_mul]
  unfold Evaluates at h ⊢
  apply (hasSum_nat_add_iff' l).1
  rw [hz, sub_zero]
  refine ((h.mul_left (x ^ l)).mul_left s).congr_fun fun k => ?_
  rw [coeff_C_mul, coeff_X_pow_mul, pow_add]
  ring

private theorem eval_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ⟦X⟧) (g : ι → ℝ) {x : ℝ}
    (h : ∀ i ∈ t, Evaluates (f i) x (g i)) : Evaluates (∑ i ∈ t, f i) x (∑ i ∈ t, g i) := by
  unfold Evaluates at h ⊢
  refine (hasSum_sum h).congr_fun fun k => ?_
  rw [map_sum, sum_mul]

private theorem eval_sub {f g : ℝ⟦X⟧} {x y z : ℝ} (hf : Evaluates f x y)
    (hg : Evaluates g x z) : Evaluates (f - g) x (y - z) := by
  unfold Evaluates at *
  exact (hf.sub hg).congr_fun fun k => by rw [map_sub, sub_mul]

private theorem eval_L {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Evaluates L x (Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x)) := by
  unfold Evaluates
  apply (hasSum_nat_add_iff' 1).1
  simpa only [sum_range_one, L, coeff_zero_X_mul, coeff_succ_X_mul, coeff_mk, zero_mul, sub_zero]
    using hasSum_b hx0 hx1

private theorem eval_P {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Evaluates P x (Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x))) := by
  have hL := eval_L hx0 hx1
  have hX := eval_shift hL 1 1
  simp only [map_one, one_mul, pow_one] at hX
  rw [P, sub_mul, one_mul]
  convert eval_sub hL hX using 1
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  rw [Real.sqrt_mul hx0.le, Real.sqrt_div hx0.le]
  field_simp [Real.sqrt_ne_zero'.mpr hpos]
  rw [Real.sq_sqrt hpos.le]

private theorem eval_M_mul (d : ℕ) {f : ℝ⟦X⟧} {x y : ℝ} (h : Evaluates f x y) :
    Evaluates (M d * f) x (zuritaM d x * y) := by
  have hm : M d = ∑ k ∈ range d, C (zuritaMCoeff d k : ℝ) * X ^ k := by
    ext k
    simp only [coeff_M, map_sum, coeff_C_mul_X_pow, sum_ite_eq, mem_range]
  rw [hm, sum_mul, zuritaM, sum_mul]
  apply eval_sum
  intro i _
  rw [mul_assoc, mul_assoc]
  exact eval_shift h _ _

private theorem eval_K_mul (n : ℕ) {f : ℝ⟦X⟧} {x y : ℝ} (h : Evaluates f x y) :
    Evaluates (K n * f) x ((∑ l ∈ range n, sReal n l * zuritaM (n - l) x * x ^ l) * y) := by
  rw [K, sum_mul, sum_mul]
  apply eval_sum
  intro i _
  rw [mul_assoc, mul_assoc]
  convert eval_shift (eval_M_mul (n - i) h) (sReal n i) i using 1
  ring

private noncomputable def aSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun k => PowerSeries.coeff k A)

private theorem radius_aSeries : 1 ≤ aSeries.radius := by
  apply aSeries.le_radius_of_bound (r := 1) 1
  intro k
  simp only [NNReal.coe_one, one_pow, mul_one, aSeries, FormalMultilinearSeries.ofScalars_norm]
  cases k with
  | zero => simp [A]
  | succ k =>
    have hC : (0 : ℝ) < Nat.centralBinom k := by exact_mod_cast Nat.centralBinom_pos k
    have hb0 : 0 ≤ b k := by unfold b a; positivity
    have hb1 : b k ≤ 1 := by
      rw [b, a, div_div, div_le_one (by positivity)]
      rw [mul_comm (Nat.centralBinom k : ℝ)]
      exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom k
    rw [coeff_A_succ, Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem enorm_lt_radius_aSeries {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ‖x‖ₑ < aSeries.radius := by
  apply lt_of_lt_of_le _ radius_aSeries
  simpa [Real.eNorm_eq_ofReal_abs, abs_of_nonneg hx0] using hx1

-- The Euler derivative of the convergent primitive is the previously evaluated series L.
private theorem hasDerivAt_aSeries_sum {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt aSeries.sum ((Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x)) / x) x := by
  have hr := enorm_lt_radius_aSeries hx0.le hx1
  have hb := (aSeries.hasFPowerSeriesOnBall (zero_le.trans_lt hr)).fderiv
  have hd := aSeries.hasFDerivAt_sum hr
  have hh := hb.hasSum (y := x) (by simpa using hr)
  rw [zero_add, aSeries.fderiv_sum hr] at hh
  have he := (ContinuousLinearMap.apply ℝ ℝ x).hasSum hh
  have he' : HasSum (fun k => b k * x ^ (k + 1)) (aSeries.derivSeries.sum x x) := by
    refine he.congr_fun fun k => ?_
    rw [ContinuousLinearMap.apply_apply, aSeries.derivSeries_apply_diag,
      show aSeries (k + 1) (fun _ => x) = (b k / ((k : ℝ) + 1)) * x ^ (k + 1) by
        rw [aSeries, FormalMultilinearSeries.ofScalars_apply_eq, coeff_A_succ, smul_eq_mul],
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have hval := he'.unique (hasSum_b hx0 hx1)
  apply hd.hasDerivAt.congr_deriv
  apply (eq_div_iff hx0.ne').2
  rw [mul_comm, ← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one, hval]

private theorem eval_A {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Evaluates A x (Real.arcsin (Real.sqrt x) ^ 2) := by
  have hf := aSeries.hasFPowerSeriesOnBall (by exact zero_lt_one.trans_le radius_aSeries)
  have hcont : ContinuousOn (fun t => aSeries.sum t - Real.arcsin (Real.sqrt t) ^ 2)
      (Set.Icc 0 x) := by
    apply (hf.continuousOn.mono ?_).sub (by fun_prop)
    intro t ht
    simpa using enorm_lt_radius_aSeries ht.1 (ht.2.trans_lt hx1)
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioo 0 x) :
      HasDerivAt (fun y => aSeries.sum y - Real.arcsin (Real.sqrt y) ^ 2) 0 t := by
    have ht1 := ht.2.trans hx1
    have hs := Real.sqrt_pos.2 ht.1
    have hs1 : Real.sqrt t < 1 := by nlinarith only [Real.sq_sqrt ht.1.le, ht1]
    have h := (((Real.hasDerivAt_arcsin (by linarith : Real.sqrt t ≠ -1) hs1.ne).comp t
      (Real.hasDerivAt_sqrt ht.1.ne')).pow 2)
    have he : 2 * Real.arcsin (Real.sqrt t) ^ (2 - 1) *
        (1 / Real.sqrt (1 - Real.sqrt t ^ 2) * (1 / (2 * Real.sqrt t))) =
          Real.sqrt (t / (1 - t)) * Real.arcsin (Real.sqrt t) / t := by
      rw [Real.sq_sqrt ht.1.le, Real.sqrt_div ht.1.le]
      norm_num only [Nat.reduceSub, pow_one]
      field_simp [hs.ne', (Real.sqrt_pos.2 (sub_pos.mpr ht1)).ne', ht.1.ne']
      rw [Real.sq_sqrt ht.1.le]
    simp only [Function.comp_apply, Nat.cast_ofNat] at h
    rw [he] at h
    change HasDerivAt (fun y => Real.arcsin (Real.sqrt y) ^ 2) _ t at h
    simpa only [sub_self] using (hasDerivAt_aSeries_sum ht.1 ht1).fun_sub h
  obtain ⟨_, _, hc⟩ := exists_hasDerivAt_eq_slope _ (fun _ => 0) hx0 hcont hderiv
  have hzero : aSeries.sum 0 = 0 := by
    change FormalMultilinearSeries.ofScalarsSum (fun k => PowerSeries.coeff k A) (0 : ℝ) = 0
    rw [FormalMultilinearSeries.ofScalarsSum_zero]
    simp [A]
  have hvalue : aSeries.sum x = Real.arcsin (Real.sqrt x) ^ 2 := by
    simp only [hzero, Real.sqrt_zero, Real.arcsin_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero] at hc
    apply sub_eq_zero.mp
    rw [← div_mul_cancel₀ (aSeries.sum x - Real.arcsin (Real.sqrt x) ^ 2) hx0.ne',
      ← hc, zero_mul]
  unfold Evaluates
  have hh := hf.hasSum (y := x) (by simpa using enorm_lt_radius_aSeries hx0.le hx1)
  rw [zero_add, hvalue] at hh
  simpa only [aSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hh

private theorem eval_F (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Evaluates (F n) x (sReal n n * x ^ n * Real.arcsin (Real.sqrt x) ^ 2 -
      Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x)) *
        ∑ l ∈ range n, sReal n l * zuritaM (n - l) x * x ^ l) := by
  rw [F, mul_comm P]
  convert eval_sub (eval_shift (eval_A hx0 hx1) (sReal n n) n)
    (eval_K_mul n (eval_P hx0 hx1)) using 1
  ring

private theorem tsum_split_F (n : ℕ) (hn : 0 < n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + n + 1)) =
      sReal n n * x ^ n * Real.arcsin (Real.sqrt x) ^ 2 -
        Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x)) *
          (∑ l ∈ range n, sReal n l * zuritaM (n - l) x * x ^ l) +
        ∑ k ∈ Icc 1 (n - 1), rCoeff n k * x ^ k + qCoeff n * x ^ n := by
  have h := eval_F n hx0 hx1
  unfold Evaluates at h
  have hsplit := h.summable.sum_add_tsum_nat_add (n + 1)
  rw [h.tsum_eq, sum_range_succ, coeff_F_diag n hn] at hsplit
  have htail : (∑' k : ℕ, PowerSeries.coeff (k + (n + 1)) (F n) * x ^ (k + (n + 1))) =
      ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + n + 1)) := by
    apply tsum_congr
    intro k
    rw [← add_assoc, coeff_F_above _ _ (by omega), a]
    push_cast
    rw [show (k : ℝ) + n + 1 - n = (k : ℝ) + 1 by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have hlow : (∑ k ∈ range n, PowerSeries.coeff k (F n) * x ^ k) =
      -(∑ k ∈ Icc 1 (n - 1), rCoeff n k * x ^ k) := by
    rw [← sum_subset (show Icc 1 (n - 1) ⊆ range n from by
      intro k hk
      have hk' := (mem_Icc.mp hk).2
      exact mem_range.mpr (by omega)), ← sum_neg_distrib]
    · apply sum_congr rfl
      intro k hk
      have hk' := mem_Icc.mp hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [coeff_F_below _ _ (by omega), neg_mul]
    · intro k hk hkn
      have hk' := mem_range.mp hk
      have hk0 : k = 0 := by
        rw [mem_Icc] at hkn
        omega
      rw [hk0, coeff_F_zero, zero_mul]
  rw [htail, hlow] at hsplit
  linear_combination hsplit

end ZuritaSquaredSeries

open ZuritaSquaredSeries

public section

/-- **Zurita's series $\sum_{k > n} 4^k x^k / ((k - n)^2\binom{2k}{k})$.** For $j \ge 1$ write
Zurita's polynomials as $S_j(x) = \sum_{k=0}^{j} s^{(j)}_k x^k$,
$T_{j-2}(x) = \sum_{k=0}^{j-2} t^{(j)}_k x^k$ and $M_{j-1}(x) = \sum_{k=0}^{j-1} m^{(j)}_k x^k$.
Let $n \ge 1$, let $x$ be real with $0 < x < 1$, and put
$$
r_k = \frac{t^{(n)}_{k-1}}{k - n} +
\frac{1}{2(k - n)} \sum_{l=0}^{k-1} s^{(n)}_l\, m^{(n-l)}_{k-l-1} +
\frac{4^k}{(k - n)^2} \Bigl(4^{-k} - \frac{1}{\binom{2k}{k}}\Bigr)
$$
for $1 \le k \le n - 1$ and
$$
q = -\frac{2^{2n+1}}{\binom{2n}{n}} + \sum_{l=0}^{n-2} s^{(n)}_l \Bigl(
\frac{4^{n-l}}{(n - l)\binom{2(n-l)}{n-l}} -
\frac12 \sum_{p=1}^{n-l-1} \frac{4^p\, m^{(n-l)}_{n-l-1-p}}{p(2p + 1)\binom{2p}{p}}\Bigr).
$$
Then
$$
\sum_{k > n} \frac{4^k x^k}{(k - n)^2 \binom{2k}{k}} =
\frac{2^{2n+1} x^n}{\binom{2n}{n}} \arcsin(\sqrt{x})^2 -
\arcsin(\sqrt{x}) \sqrt{x(1 - x)} \sum_{k=0}^{n-1} s^{(n)}_k M_{n-k-1}(x)\, x^k +
\sum_{k=1}^{n-1} r_k x^k + q x^n.
$$

The source states the identity for $|x| < 1$; this statement is its case $0 < x < 1$, where
$\sqrt{x}$ is real.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 2 (`integers-2026-A2-cor-2`). -/
theorem tsum_four_pow_div_sub_sq_mul_centralBinom {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    let r : ℕ → ℝ := fun k =>
      ((zuritaTCoeff n (k - 1) : ℝ) / ((k : ℝ) - n) +
          1 / 2 * ∑ l ∈ range k, (zuritaSCoeff n l * zuritaMCoeff (n - l) (k - l - 1) : ℝ) /
            ((k : ℝ) - n)) +
        (4 : ℝ) ^ k / ((k : ℝ) - n) ^ 2 * (1 / (4 : ℝ) ^ k - 1 / Nat.centralBinom k)
    let q : ℝ := -(2 : ℝ) ^ (2 * n + 1) / Nat.centralBinom n +
      ∑ l ∈ range (n - 1), (zuritaSCoeff n l : ℝ) *
        ((4 : ℝ) ^ (n - l) / (((n - l : ℕ) : ℝ) * Nat.centralBinom (n - l)) -
          1 / 2 * ∑ p ∈ Icc 1 (n - l - 1),
            (4 : ℝ) ^ p * (zuritaMCoeff (n - l) (n - l - 1 - p) : ℝ) /
              ((p : ℝ) * (2 * p + 1) * Nat.centralBinom p))
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + n + 1)) =
      (2 : ℝ) ^ (2 * n + 1) * x ^ n / Nat.centralBinom n * Real.arcsin (Real.sqrt x) ^ 2 -
        Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x)) *
          ∑ k ∈ range n, (zuritaSCoeff n k : ℝ) * zuritaM (n - k) x * x ^ k +
        ∑ k ∈ Icc 1 (n - 1), r k * x ^ k + q * x ^ n := by
  dsimp only
  have hlead : (2 : ℝ) ^ (2 * n + 1) / Nat.centralBinom n = 2 * a n := by
    rw [a, pow_succ, pow_mul]
    norm_num
    ring
  have hr (k : ℕ) : (1 - a k) / ((k : ℝ) - n) ^ 2 =
      (4 : ℝ) ^ k / ((k : ℝ) - n) ^ 2 * (1 / (4 : ℝ) ^ k - 1 / Nat.centralBinom k) := by
    rw [a]
    have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
    simp only [div_eq_mul_inv, one_mul]
    rw [mul_sub, mul_right_comm, mul_inv_cancel₀ h4, one_mul]
    ring
  have hb (p d : ℕ) : b p * (zuritaMCoeff d (d - 1 - p) : ℝ) / (p : ℝ) =
      (4 : ℝ) ^ p * (zuritaMCoeff d (d - 1 - p) : ℝ) /
        ((p : ℝ) * (2 * p + 1) * Nat.centralBinom p) := by
    rw [b, a]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have h := tsum_split_F n hn hx0 hx1
  rw [s_last n hn, ← hlead] at h
  simp only [rCoeff, qCoeff, ← hlead, hr, hb, sReal] at h
  simp only [a, div_div, mul_comm (Nat.centralBinom _ : ℝ), neg_div,
    div_mul_eq_mul_div] at h ⊢
  exact h

end

end MetaMathlibExt
