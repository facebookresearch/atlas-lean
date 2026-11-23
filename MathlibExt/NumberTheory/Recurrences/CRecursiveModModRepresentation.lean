/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Polynomial

/-!
# A double remainder for rational generating functions

For a proper rational generating function with natural coefficients, evaluation at a small
reciprocal base separates a finite block of digits from a strictly positive tail. Reducing
the resulting integer identity twice gives the sign-dependent representation of Prunescu
and Shunia.
-/

public section

namespace MetaMathlibExt

namespace exists_mod_mod_representation_sign

open Finset Polynomial

private theorem positive_in_tail {t : ℕ → ℕ} {A B : Polynomial ℤ}
    (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (m : ℕ) : ∃ j, 0 < t (j + m) := by
  by_contra! h
  let f := PowerSeries.mk fun n => (t n : ℤ)
  have hf : (f.trunc m : PowerSeries ℤ) = f := by
    ext k
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hk
    · rfl
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hk)
      simp [f, add_comm m j, Nat.eq_zero_of_le_zero (h j)]
  have he : f.trunc m * B = A := by
    apply Polynomial.coe_injective ℤ
    simpa only [Polynomial.coe_mul, hf] using hgf
  have hf0 : f.trunc m ≠ 0 := fun h0 => hA (by simp [← he, h0])
  have hB : B ≠ 0 := by rintro rfl; simp at hAB
  rw [← he, natDegree_mul hf0 hB] at hAB
  omega

private theorem polynomial_hasSum (P : Polynomial ℤ) (z : ℝ) :
    HasSum (fun k => (P.coeff k : ℝ) * z ^ k) (P.eval₂ (Int.castRingHom ℝ) z) := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hk : P.natDegree < k)]
  simp

private theorem eval_generating_function {t : ℕ → ℕ} {A B : Polynomial ℤ} {z : ℝ}
    (hz : 0 ≤ z) (hs : Summable fun k => (t k : ℝ) * z ^ k)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ)) :
    (∑' k, (t k : ℝ) * z ^ k) * B.eval₂ (Int.castRingHom ℝ) z =
      A.eval₂ (Int.castRingHom ℝ) z := by
  have ht : Summable fun k => ‖(t k : ℝ) * z ^ k‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))]
      using hs
  rw [← (polynomial_hasSum B z).tsum_eq,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ht
      (summable_abs_iff.mpr (polynomial_hasSum B z).summable), ← (polynomial_hasSum A z).tsum_eq]
  apply tsum_congr
  intro k
  have he := congrArg (PowerSeries.coeff k) hgf
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Polynomial.coeff_coe] at he
  rw [← he, Int.cast_sum, sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  push_cast
  ring

private theorem eval_reverse {q : ℤ} (hq : 0 < q) (P : Polynomial ℤ) :
    ((P.reverse.eval q : ℤ) : ℝ) =
      (q : ℝ) ^ P.natDegree * P.eval₂ (Int.castRingHom ℝ) (q : ℝ)⁻¹ := by
  have h : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  let := invertibleOfNonzero (inv_ne_zero h)
  have he := Polynomial.eval₂_reverse_mul_pow (Int.castRingHom ℝ) (q : ℝ)⁻¹ P
  rw [invOf_eq_inv, inv_inv] at he
  change P.reverse.eval₂ _ ((Int.castRingHom ℝ) q) * _ = _ at he
  rw [Polynomial.eval₂_at_apply, inv_pow] at he
  rw [← he]
  field_simp
  rfl

-- After multiplication by qⁿ, the first n + 1 terms are an integer; the remaining
-- terms lie strictly between 0 and 1. A geometric majorant works uniformly in n.
private theorem digit_bounds {t : ℕ → ℕ} {b n : ℕ} {q : ℤ}
    (hq : 0 < q) (ht : ∀ k, 1 ≤ k → t k ≤ b ^ k)
    (htail : ∃ j, 0 < t (j + (n + 1)))
    (hbq : (b : ℝ) / q ≤ 1 / 2) (hnq : (b : ℝ) ^ (n + 1) / q ≤ 1 / 4) :
    Summable (fun k => (t k : ℝ) * (q : ℝ)⁻¹ ^ k) ∧
      ∃ s : ℤ, s ≡ t n [ZMOD q] ∧
        (s : ℝ) < (q : ℝ) ^ n * ∑' k, (t k : ℝ) * (q : ℝ)⁻¹ ^ k ∧
        (q : ℝ) ^ n * (∑' k, (t k : ℝ) * (q : ℝ)⁻¹ ^ k) < s + 1 := by
  let tail (j : ℕ) := (t (j + (n + 1)) : ℝ) / (q : ℝ) ^ (j + 1)
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hnneg (j) : 0 ≤ tail j := by dsimp [tail]; positivity
  have hmajor (j) : tail j ≤ 1 / 4 * (1 / 2 : ℝ) ^ j := by
    calc
      tail j ≤ (b : ℝ) ^ (j + (n + 1)) / (q : ℝ) ^ (j + 1) := by
        dsimp only [tail]
        gcongr
        exact_mod_cast ht _ (by omega)
      _ = ((b : ℝ) ^ (n + 1) / q) * (b / (q : ℝ)) ^ j := by
        rw [pow_add, pow_succ (q : ℝ), div_pow]
        ring
      _ ≤ _ := by gcongr
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).mul_left (1 / 4)
  have hs := hg.summable.of_nonneg_of_le hnneg hmajor
  obtain ⟨j, hj⟩ := htail
  have hpos := hs.tsum_pos hnneg j (by dsimp [tail]; positivity)
  have hlt : ∑' j, tail j < 1 := by
    have := hs.tsum_le_tsum hmajor hg.summable
    rw [hg.tsum_eq] at this
    linarith
  let f (k : ℕ) := (t k : ℝ) * (q : ℝ)⁻¹ ^ k
  have hshift (i : ℕ) : f (i + (n + 1)) = (q : ℝ)⁻¹ ^ n * tail i := by
    dsimp [f, tail]
    rw [pow_add]
    simp only [pow_succ, inv_pow]
    field_simp
  have hf : Summable f := (summable_nat_add_iff (n + 1)).mp <|
    (hs.mul_left _).congr fun i => (hshift i).symm
  let s : ℤ := ∑ k ∈ range (n + 1), (t k : ℤ) * q ^ (n - k)
  refine ⟨hf, s, ?_, ?_⟩
  · dsimp [s]
    rw [sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    have hd : q ∣ ∑ k ∈ range n, (t k : ℤ) * q ^ (n - k) := by
      apply dvd_sum
      intro k hk
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by have := mem_range.mp hk; omega)) _
    simpa using (Int.modEq_zero_iff_dvd.mpr hd).add_right (t n : ℤ)
  · have he : (q : ℝ) ^ n * (∑' k, f k) = s + ∑' i, tail i := by
      rw [← hf.sum_add_tsum_nat_add (n + 1), mul_add]
      congr 1
      · dsimp only [s]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        have hkn : k ≤ n := by simpa using hk
        dsimp [f]
        conv_lhs => rw [← Nat.sub_add_cancel hkn, pow_add]
        rw [inv_pow]
        field_simp
      · simp_rw [hshift, tsum_mul_left, ← mul_assoc, inv_pow]
        field_simp
    change (_ < (q : ℝ) ^ n * (∑' k, f k)) ∧ ((q : ℝ) ^ n * (∑' k, f k) < _)
    rw [he]
    constructor <;> linarith

private theorem sign_formula {P D q a s : ℤ} {v : ℕ}
    (ha : a ≠ 0) (hP : P ≡ 0 [ZMOD q]) (hD : D ≡ a [ZMOD q]) (hs : s ≡ v [ZMOD q])
    (hl : D * s < P) (hu : P < D * (s + 1)) (hv : |a| * (v + 1) < q) :
    (v : ℚ) = (-1 - a.sign : ℚ) / 2 +
      (1 / |(a : ℚ)|) * (((-a.sign * P) % D % q : ℤ) : ℚ) := by
  rcases lt_or_gt_of_ne ha with h | h
  · have hrem : P % D = P - D * s := by
      rw [← Int.sub_mul_emod_self_left P D s, Int.emod_eq_of_lt] <;> linarith
    have hres : (P - D * s) % q = (-a) * v := by
      have he := (hP.sub (hD.mul hs)).eq
      rw [zero_sub, ← neg_mul] at he
      rw [he, Int.emod_eq_of_lt]
      · exact mul_nonneg (neg_nonneg.mpr h.le) (Int.natCast_nonneg _)
      · rw [abs_of_neg h] at hv
        linarith
    have h' : (a : ℚ) < 0 := by exact_mod_cast h
    rw [Int.sign_eq_neg_one_of_neg h, neg_neg, one_mul, hrem, hres, abs_of_neg h']
    push_cast
    field_simp
    ring
  · have hrem : (-P) % D = -P + D * (s + 1) := by
      rw [← Int.add_mul_emod_self_left (-P) D (s + 1), Int.emod_eq_of_lt] <;> linarith
    have hres : (-P + D * (s + 1)) % q = a * (v + 1) := by
      have he := (hP.neg.add (hD.mul (hs.add_right 1))).eq
      simp only [neg_zero, zero_add] at he
      rw [he, Int.emod_eq_of_lt]
      · positivity
      · simpa [abs_of_pos h] using hv
    have h' : 0 < (a : ℚ) := by exact_mod_cast h
    rw [Int.sign_eq_one_of_pos h, neg_one_mul, hrem, hres, abs_of_pos h']
    push_cast
    field_simp
    ring

open Filter in
private theorem eventually_pos_denominator {B : Polynomial ℤ} (hB0 : B.coeff 0 = 1) :
    ∃ m : ℕ, ∀ q : ℕ, m ≤ q → 0 < B.eval₂ (Int.castRingHom ℝ) (q : ℝ)⁻¹ := by
  have he := (B.continuous_eval₂ (Int.castRingHom ℝ)).continuousAt (x := 0)
  have ht := he.tendsto.comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  apply eventually_atTop.mp (ht.eventually_const_lt ?_)
  simp [Polynomial.eval₂_at_zero, hB0]

end exists_mod_mod_representation_sign

open exists_mod_mod_representation_sign in
/--
**Single-formula mod-mod representation of C-recursive sequences.** Let
$t_0, t_1, t_2, \dots$ be natural numbers, let $c$ be a natural number, and let $A$ and $B$ be
polynomials with integer coefficients such that $A \ne 0$, $B(0) = 1$ and
$k = \deg A < d = \deg B$. Suppose that $\bigl(\sum_{n \ge 0} t_n z^n\bigr) B(z) = A(z)$ as
formal power series. Let $\tilde A(x) = x^k A(1/x)$ and $\tilde B(x) = x^d B(1/x)$ be the
reversed polynomials, let $\alpha$ be the constant term of $\tilde B$, that is, the leading
coefficient of $B$, and for an integer $x$ put $P_x(n) = x^{n^2} x^{n(d-k)} \tilde A(x^n)$. For
integers $X$ and $M \ne 0$, write $X \bmod M$ for the remainder of $X$ modulo $M$ in
$\{0, 1, \dots, |M| - 1\}$, and set $X \bmod 0 = X$. Suppose that for every $n \ge 1$,

$$t_n = \bigl\lfloor P_c(n) / \tilde B(c^n) \bigr\rfloor \bmod c^n,$$

where the quotient is taken in $\mathbb{Q}$ and is $0$ when $\tilde B(c^n) = 0$. Put
$\sigma = \operatorname{sgn} \alpha$; note $\alpha \ne 0$ because $B \ne 0$. Then there is a
natural number $r \ge c$ such that for every $n \ge 1$, writing
$\rho_n = \bigl( (-\sigma P_r(n)) \bmod \tilde B(r^n) \bigr) \bmod r^n$, the rational numbers
satisfy

$$t_n = \frac{-1 - \sigma}{2} + \frac{\rho_n}{|\alpha|}.$$

The hypothesis $A \ne 0$ excludes the zero sequence: for $A = 0$ and $B(z) = 1 + z$ the right
side is $-1$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 9.
-/
theorem exists_mod_mod_representation_sign
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n) :
    ∃ r : ℕ, c ≤ r ∧ ∀ n, 1 ≤ n →
      (t n : ℚ) = (-1 - (B.reverse.coeff 0).sign : ℚ) / 2 +
        (1 / |(B.reverse.coeff 0 : ℚ)|) *
          (((-(B.reverse.coeff 0).sign * ((r : ℤ) ^ (n ^ 2) *
              (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) * A.reverse.eval ((r : ℤ) ^ n))) %
            B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n : ℤ) : ℚ) := by
  let b := c + 2
  have hb : 2 ≤ b := by dsimp [b]; omega
  have ht (k : ℕ) (hk : 1 ≤ k) : t k ≤ b ^ k := by
    have h := hrep k hk
    by_cases hc : c = 0
    · subst c
      have hk' : k ≠ 0 := by omega
      simp [hk'] at h
      simp [h]
    · have hpos : 0 < (c : ℤ) ^ k := by positivity
      have hlt : (t k : ℤ) < (c : ℤ) ^ k := h.trans_lt (Int.emod_lt_of_pos _ hpos)
      exact (show t k < c ^ k by exact_mod_cast hlt).le.trans
        (Nat.pow_le_pow_left (by dsimp [b]; omega) _)
  let a := B.reverse.coeff 0
  have ha : a ≠ 0 := by
    rw [show a = B.leadingCoeff from Polynomial.coeff_zero_reverse B]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    rintro rfl
    simp at hB0
  obtain ⟨m, hm⟩ := eventually_pos_denominator hB0
  let r := max (max c m) ((4 + a.natAbs) * b ^ 2)
  refine ⟨r, (le_max_left c m).trans (le_max_left ..), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  let q := r ^ n
  have hrq : r ≤ q := Nat.le_self_pow hn0 r
  have hsize : (4 + a.natAbs) * b ^ (n + 1) ≤ q := calc
    _ ≤ (4 + a.natAbs) ^ n * b ^ (2 * n) :=
      Nat.mul_le_mul (Nat.le_self_pow hn0 _) (Nat.pow_le_pow_right (by omega) (by omega))
    _ = ((4 + a.natAbs) * b ^ 2) ^ n := by rw [mul_pow, pow_mul]
    _ ≤ q := Nat.pow_le_pow_left (le_max_right ..) n
  have hbpow : b ≤ b ^ (n + 1) := Nat.le_self_pow (by omega) _
  have hsmall : 4 * b ^ (n + 1) ≤ q :=
    (Nat.mul_le_mul_right _ (by omega : 4 ≤ 4 + a.natAbs)).trans hsize
  have hq : 0 < q := by omega
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨hsum, s, hs, hl, hu⟩ := digit_bounds (q := (q : ℤ)) (by exact_mod_cast hq) ht
    (positive_in_tail hAB hA hgf (n + 1))
    (by
      simp only [Int.cast_natCast, div_le_div_iff₀ hqr (by norm_num : (0 : ℝ) < 2), one_mul]
      exact_mod_cast (show b * 2 ≤ q by omega))
    (by
      simp only [Int.cast_natCast, div_le_div_iff₀ hqr (by norm_num : (0 : ℝ) < 4), one_mul]
      exact_mod_cast (mul_comm 4 _ ▸ hsmall))
  let D := B.reverse.eval (q : ℤ)
  let P := (q : ℤ) ^ n * (q : ℤ) ^ (B.natDegree - A.natDegree) * A.reverse.eval (q : ℤ)
  let F := ∑' k, (t k : ℝ) * (q : ℝ)⁻¹ ^ k
  simp only [Int.cast_natCast] at hsum hl hu
  have hrev (p : Polynomial ℤ) := eval_reverse (q := (q : ℤ)) (by exact_mod_cast hq) p
  simp only [Int.cast_natCast] at hrev
  have hBpos := hm q (((le_max_right c m).trans (le_max_left ..)).trans hrq)
  have hDpos : 0 < (D : ℝ) := by
    rw [show (D : ℝ) = _ from hrev B]
    exact mul_pos (pow_pos hqr _) hBpos
  have he := eval_generating_function (inv_nonneg.mpr hqr.le) hsum hgf
  have hval : (P : ℝ) = (q : ℝ) ^ n * F * D := by
    dsimp only [P, D]
    push_cast
    rw [hrev A, hrev B, ← he]
    dsimp only [F]
    have hpow : (q : ℝ) ^ (B.natDegree - A.natDegree) * (q : ℝ) ^ A.natDegree =
        (q : ℝ) ^ B.natDegree := by rw [← pow_add, Nat.sub_add_cancel hAB.le]
    rw [← hpow]
    ring
  have hP : P ≡ 0 [ZMOD (q : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_pow_self _ hn0) _) _
  have hD : D ≡ a [ZMOD (q : ℤ)] := by
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    simpa only [D, a, sub_zero, Polynomial.coeff_zero_eq_eval_zero] using
      B.reverse.sub_dvd_eval_sub (q : ℤ) 0
  have hv : a.natAbs * (t n + 1) < q := by
    have hbn : 0 < b ^ n := pow_pos (by omega) _
    have htn := ht n hn
    have hle : t n + 1 ≤ b ^ (n + 1) := by rw [pow_succ]; nlinarith
    exact (Nat.mul_le_mul_left _ hle).trans_lt <|
      (Nat.mul_lt_mul_of_pos_right (by omega : a.natAbs < 4 + a.natAbs) (by positivity)).trans_le
        hsize
  have hlow : (D : ℝ) * s < P := by
    rw [hval, mul_comm (D : ℝ)]
    exact mul_lt_mul_of_pos_right hl hDpos
  have hhigh : (P : ℝ) < D * ((s : ℝ) + 1) := by
    rw [hval, mul_comm (D : ℝ)]
    exact mul_lt_mul_of_pos_right hu hDpos
  have hbound : |a| * ((t n : ℤ) + 1) < q := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hv
  have hresult := sign_formula ha hP hD hs (by exact_mod_cast hlow) (by exact_mod_cast hhigh)
    hbound
  simpa only [P, D, q, a, Nat.cast_pow, ← pow_mul, pow_two] using hresult

end MetaMathlibExt
