/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.WLOG
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula

/-!
# Prime terms of Lucas sequences with power parameters

If both characteristic roots are the same higher powers of real roots with integral sum and
product, the Lucas sequence has only finitely many prime absolute values under the stated
positivity assumptions. The proof compares two integer factorizations of the same Lucas term.
-/

namespace MetaMathlibExt

namespace lucasU_power_params_finite_primes

/-- Taking the powers of the roots corresponds to taking a subsequence and normalizing. -/
private theorem mul_index (L M : LucasSequenceParams) {x y : ℝ} {k : ℕ}
    (hs : x + y = L.p) (hp : x * y = L.q)
    (hs' : x ^ k + y ^ k = M.p) (hp' : x ^ k * y ^ k = M.q)
    (hne : x ^ k ≠ y ^ k) (n : ℕ) :
    lucasU L (k * n) = lucasU L k * lucasU M n := by
  have hxy : x ≠ y := fun h ↦ hne (congrArg (· ^ k) h)
  have hL (m : ℕ) := ((lucas_binet_formulas_of_field L x y hs hp).1 hxy m).1
  have hM := ((lucas_binet_formulas_of_field M (x ^ k) (y ^ k) hs' hp').1 hne n).1
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_mul, hL, hL, hM, pow_mul, pow_mul]
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hne]

/-- The absolute difference of the powers is bounded above and below by fixed positive
multiples of the power of the larger absolute value. -/
private theorem power_difference_bounds {x y : ℝ} (hdom : |y| < |x|) {n : ℕ} (hn : 0 < n) :
    (1 - |y| / |x|) * |x| ^ n ≤ |x ^ n - y ^ n| ∧ |x ^ n - y ^ n| ≤ 2 * |x| ^ n := by
  have hx : 0 < |x| := (abs_nonneg y).trans_lt hdom
  have hratio : |y| / |x| < 1 := (div_lt_one hx).mpr hdom
  have hsmall : |y| ^ n ≤ (|y| / |x|) * |x| ^ n := by
    apply (div_le_iff₀ (pow_pos hx n)).mp
    rw [← div_pow]
    simpa only [pow_one] using
      pow_le_pow_of_le_one (div_nonneg (abs_nonneg y) hx.le) hratio.le hn
  constructor
  · calc
      (1 - |y| / |x|) * |x| ^ n ≤ |x| ^ n - |y| ^ n := by linarith only [hsmall]
      _ ≤ |x ^ n - y ^ n| := by simpa only [abs_pow] using abs_sub_abs_le_abs_sub (x ^ n) (y ^ n)
  · calc
      |x ^ n - y ^ n| ≤ |x| ^ n + |y| ^ n := by
        simpa [abs_pow] using abs_sub_le (x ^ n) 0 (y ^ n)
      _ ≤ 2 * |x| ^ n := by linarith only [pow_le_pow_left₀ (abs_nonneg y) hdom.le n]

private theorem natAbs_eq (L : LucasSequenceParams) {x y : ℝ} (n : ℕ)
    (h : (lucasU L n : ℝ) = (x ^ n - y ^ n) / (x - y)) :
    ((lucasU L n).natAbs : ℝ) = |x ^ n - y ^ n| / |x - y| := by
  rw [Nat.cast_natAbs, Int.cast_abs, h, abs_div]

/-- A prime multiplied by a cofactor cannot split into two factors both exceeding the cofactor. -/
private theorem not_prime_of_mul_eq {c p d e : ℕ} (h : c * p = d * e) (hd : c < d) (he : c < e) :
    ¬ p.Prime := by
  intro hp
  have hdiv : p ∣ d * e := h ▸ dvd_mul_left p c
  have impossible {u v : ℕ} (hu : c < u) (hv : c < v)
      (huv : c * p = u * v) (hpv : p ∣ v) : False := by
    have hlt := calc
      c * p < u * p := Nat.mul_lt_mul_of_pos_right hu hp.pos
      _ ≤ u * v := Nat.mul_le_mul_left u (Nat.le_of_dvd ((Nat.zero_le c).trans_lt hv) hpv)
    exact (ne_of_lt hlt) huv
  rcases hp.dvd_mul.mp hdiv with hpd | hpe
  · exact impossible he hd (h.trans (Nat.mul_comm d e)) hpd
  · exact impossible hd he h hpe

end lucasU_power_params_finite_primes

open lucasU_power_params_finite_primes

/-- **Lucas sequences with power parameters have finitely many prime terms.** Let $x \ne y$
be real numbers such that $x + y$ and $xy$ are integers, and let $r > 1$ be a natural
number. Let $P$ and $Q$ be integers with $P = x^r + y^r$ and $Q = x^r y^r$, and suppose
$Q \ne 0$, $P \ge 1$ and $P^2 - 4Q > 0$. Let $U_n = U_n(P, Q)$ be the Lucas sequence with
$U_0 = 0$, $U_1 = 1$ and $U_{n+2} = PU_{n+1} - QU_n$. Then $|U_n|$ is prime for only
finitely many natural numbers $n$.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 4(b)
(quoted from their reference [2]) (`integers-2025-A42-thm-4`). -/
public theorem lucasU_power_params_finite_primes {x y : ℝ} (hxy : x ≠ y) {a b : ℤ}
    (hs : x + y = a) (hp : x * y = b) {r : ℕ} (hr : 1 < r) {P Q : ℤ} (hQ : Q ≠ 0)
    (hPdef : (P : ℝ) = x ^ r + y ^ r) (hQdef : (Q : ℝ) = x ^ r * y ^ r) (hP : 1 ≤ P)
    (hD : 0 < P ^ 2 - 4 * Q) :
    {n : ℕ | (lucasU ⟨P, Q, hQ⟩ n).natAbs.Prime}.Finite := by
  wlog horder : |y| ≤ |x| generalizing x y
  · exact this hxy.symm (by simpa only [add_comm] using hs) (by simpa only [mul_comm] using hp)
      (by simpa only [add_comm] using hPdef) (by simpa only [mul_comm] using hQdef)
      (le_of_not_ge horder)
  have hDreal : (0 : ℝ) < (P : ℝ) ^ 2 - 4 * (Q : ℝ) := by exact_mod_cast hD
  rw [hPdef, hQdef, show (x ^ r + y ^ r) ^ 2 - 4 * (x ^ r * y ^ r) =
    (x ^ r - y ^ r) ^ 2 by ring] at hDreal
  have hpow : x ^ r ≠ y ^ r := by
    intro h
    simp [h] at hDreal
  have habs : |x| ≠ |y| := by
    intro h
    have habsPow : |x ^ r| = |y ^ r| := by simp only [abs_pow, h]
    rcases abs_eq_abs.mp habsPow with heq | heq
    · exact hpow heq
    · have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
      linarith only [hPpos, hPdef, heq]
  have hdom : |y| < |x| := lt_of_le_of_ne horder habs.symm
  have hQb : Q = b ^ r := by
    exact_mod_cast (show (Q : ℝ) = (b : ℝ) ^ r by rw [hQdef, ← mul_pow, hp])
  have hb : b ≠ 0 := fun h ↦ hQ (by rw [hQb, h, zero_pow (by omega)])
  have hx : 1 < |x| := by
    have hbabs : (1 : ℝ) ≤ |(b : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast (show (1 : ℤ) ≤ |b| from abs_pos.mpr hb)
    rw [← hp, abs_mul] at hbabs
    by_contra! hx
    have hlt : |y| * |x| < 1 := calc
      _ < |x| * |x| := mul_lt_mul_of_pos_right hdom ((abs_nonneg y).trans_lt hdom)
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hx (abs_nonneg x)
      _ ≤ 1 := by simpa using hx
    exact hlt.not_ge (by simpa only [mul_comm] using hbabs)
  let L : LucasSequenceParams := ⟨a, b, hb⟩
  let M : LucasSequenceParams := ⟨P, Q, hQ⟩
  have hL := (lucas_binet_formulas_of_field L x y hs hp).1 hxy
  let c := (lucasU L r).natAbs
  let δ := 1 - |y| / |x|
  have hδ : 0 < δ := sub_pos.mpr ((div_lt_one (by positivity)).mpr hdom)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max ((c : ℝ) * |x - y|) (2 * c) / δ) hx
  apply (Set.finite_lt_nat (N + 1)).subset
  intro n hn
  change (lucasU M n).natAbs.Prime at hn
  change n < N + 1
  by_contra! hlarge
  have hnpos : 0 < n := by omega
  have hlarge' : max ((c : ℝ) * |x - y|) (2 * c) < δ * |x| ^ n := by
    rw [mul_comm δ]
    exact (div_lt_iff₀ hδ).mp (hN.trans_le (pow_le_pow_right₀ hx.le (by omega)))
  obtain ⟨hnLower, hnUpper⟩ := power_difference_bounds hdom hnpos
  have hne : x ^ n ≠ y ^ n := by
    have hlt := pow_lt_pow_left₀ hdom (abs_nonneg y) hnpos.ne'
    rw [← abs_pow, ← abs_pow] at hlt
    exact fun h ↦ hlt.ne' (congrArg abs h)
  let K : LucasSequenceParams := ⟨lucasV L n, b ^ n, pow_ne_zero n hb⟩
  have hKs : x ^ n + y ^ n = (K.p : ℝ) := (hL n).2.symm
  have hKp : x ^ n * y ^ n = (K.q : ℝ) := by simp only [K, Int.cast_pow, ← hp, mul_pow]
  have hK := (lucas_binet_formulas_of_field K (x ^ n) (y ^ n) hKs hKp).1 hne
  -- The two ways of taking powers give the same term at index `r * n`.
  have hfactor : lucasU L r * lucasU M n = lucasU L n * lucasU K r := calc
    _ = lucasU L (r * n) := (mul_index L M hs hp hPdef.symm hQdef.symm hpow n).symm
    _ = lucasU L (n * r) := by rw [Nat.mul_comm]
    _ = _ := mul_index L K hs hp hKs hKp hne r
  have hd : c < (lucasU L n).natAbs := by
    have hlt : (c : ℝ) < ((lucasU L n).natAbs : ℝ) := by
      rw [natAbs_eq L n (hL n).1]
      apply (lt_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy))).mpr
      exact ((le_max_left _ _).trans_lt hlarge').trans_le hnLower
    exact_mod_cast hlt
  have he : c < (lucasU K r).natAbs := by
    have hlt : (c : ℝ) < ((lucasU K r).natAbs : ℝ) := by
      rw [natAbs_eq K r (hK r).1, ← pow_mul, ← pow_mul]
      apply (lt_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr
      calc
        (c : ℝ) * |x ^ n - y ^ n| ≤ c * (2 * |x| ^ n) :=
          mul_le_mul_of_nonneg_left hnUpper (Nat.cast_nonneg c)
        _ = (2 * c) * |x| ^ n := by ring
        _ < (δ * |x| ^ n) * |x| ^ n :=
          mul_lt_mul_of_pos_right ((le_max_right _ _).trans_lt hlarge') (by positivity)
        _ ≤ δ * |x| ^ (n * r) := by
          rw [mul_assoc, ← pow_add]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx.le (by
            simpa only [Nat.mul_two] using Nat.mul_le_mul_left n (show 2 ≤ r by omega))) hδ.le
        _ ≤ |x ^ (n * r) - y ^ (n * r)| :=
          (power_difference_bounds hdom (Nat.mul_pos hnpos (by omega))).1
    exact_mod_cast hlt
  exact not_prime_of_mul_eq (by simpa only [Int.natAbs_mul] using congrArg Int.natAbs hfactor)
    hd he hn

end MetaMathlibExt
