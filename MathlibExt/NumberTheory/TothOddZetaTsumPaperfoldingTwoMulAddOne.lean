/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Combinatorics.ReducedComplexities
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# A paperfolding Dirichlet series at odd integers

We evaluate the Dirichlet series with regular-paperfolding coefficients at each odd integer
greater than one in terms of an even-index Euler number and a power of π.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 5 (`jis-2025-25.4.4-lem-5`);
`bₙ` read from arXiv:2508.04151v1.
-/

namespace MetaMathlibExt

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Combinatorics.ReducedComplexitiesWanted (paperfoldingSeq)

namespace tsum_paperfolding_two_mul_add_one

-- Odd Bernoulli polynomials at one quarter via an Euler-number recurrence (Zhi-Hong
-- Sun, *Super congruences involving Bernoulli and Euler polynomials*, proof of
-- Theorem 3.2).
private lemma catalanExp_hasseDeriv_bernoulli (n k : ℕ) :
    Polynomial.hasseDeriv k (Polynomial.bernoulli n) =
      (n.choose k : ℚ) • Polynomial.bernoulli (n - k) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_bernoulli,
    AddMonoidAlgebra.coeff_smul_apply, Polynomial.coeff_bernoulli]
  by_cases hik : i + k ≤ n
  · rw [ite_eq_left hik, ite_eq_left (by omega : i ≤ n - k)]
    have hc : (i + k).choose k * n.choose (i + k) =
        n.choose k * (n - k).choose i := by
      have hc' := Nat.choose_mul (n := n) (k := i + k) (s := k) (by omega)
      rw [show i + k - k = i by omega] at hc'
      simpa only [mul_comm] using hc'
    rw [show n - (i + k) = n - k - i by omega]
    have hc' : ((i + k).choose k : ℚ) * n.choose (i + k) =
        n.choose k * (n - k).choose i := by exact_mod_cast hc
    linear_combination (bernoulli (n - k - i) : ℚ) * hc'
  · rw [ite_eq_right hik]
    by_cases hk : k ≤ n
    · rw [ite_eq_right (by omega : ¬i ≤ n - k)]
      simp
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]

private lemma catalanExp_bernoulli_eval_add (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli (n - k)).eval x * y ^ k := by
  have htaylor : Polynomial.taylor x (Polynomial.bernoulli n) =
      ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k
        ((n.choose k : ℚ) * (Polynomial.bernoulli (n - k)).eval x) := by
    ext k
    rw [Polynomial.taylor_coeff, catalanExp_hasseDeriv_bernoulli,
      Polynomial.eval_smul]
    by_cases hk : k ≤ n
    · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
      · simp
      · intro b hb hbk
        rw [Polynomial.coeff_monomial_apply, ite_eq_right hbk]
      · simp [hk]
    · have hkn : n < k := by omega
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_smul,
        Polynomial.finsetSum_coeff]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hbn : b ≤ n := by simpa using (Finset.mem_range.mp hb)
      have hbk : b ≠ k := by omega
      rw [Polynomial.coeff_monomial_apply, ite_eq_right hbk]
  calc
    (Polynomial.bernoulli n).eval (x + y) =
        (Polynomial.taylor x (Polynomial.bernoulli n)).eval y := by
      rw [Polynomial.taylor_eval, add_comm]
    _ = _ := by
      rw [htaylor, Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.eval_monomial]

private lemma catalanExp_bernoulli_eval_add' (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * y ^ (n - k) := by
  rw [catalanExp_bernoulli_eval_add, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega]
  rw [show n - (n - k) = k by omega, Nat.choose_symm hkn]

private lemma catalanExp_pow_mul_inv_pow {a : ℚ} (ha : a ≠ 0) {k n : ℕ} (hkn : k ≤ n) :
    a ^ n * a⁻¹ ^ (n - k) = a ^ k := by
  rw [inv_pow, ← pow_sub_mul_pow a hkn]
  field_simp

private lemma catalanExp_sum_range_even_odd {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2), f k =
      ∑ r ∈ Finset.range (m + 1), (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
      conv_lhs =>
        rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih]
      simp only [show 2 * m + 2 = 2 * (m + 1) by omega,
        show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by omega, add_assoc]

private lemma catalanExp_bernoulli_eval_half_odd (m : ℕ) :
    (Polynomial.bernoulli (2 * m + 1)).eval (1 / 2 : ℚ) = 0 := by
  have h := Polynomial.bernoulli_eval_one_sub (2 * m + 1) (1 / 2 : ℚ)
  norm_num [Even.neg_one_pow, Odd.neg_one_pow, show Odd (2 * m + 1) from ⟨m, by omega⟩] at h
  linarith

private lemma catalanExp_bernoulli_eval_zero_odd (m : ℕ) (hm : 0 < m) :
    (Polynomial.bernoulli (2 * m + 1)).eval 0 = 0 := by
  rw [Polynomial.bernoulli_eval_zero,
    bernoulli_eq_zero_of_odd (⟨m, by omega⟩ : Odd (2 * m + 1)) (by omega)]

private lemma catalanExp_weighted_bernoulli_add (n : ℕ) (x a : ℚ) (ha : a ≠ 0) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * a ^ k =
      a ^ n * (Polynomial.bernoulli n).eval (x + a⁻¹) := by
  rw [catalanExp_bernoulli_eval_add', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  calc
    (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * a ^ k =
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x *
          (a ^ n * a⁻¹ ^ (n - k)) := by
      rw [catalanExp_pow_mul_inv_pow ha hkn]
    _ = a ^ n * ((n.choose k : ℚ) * (Polynomial.bernoulli k).eval x *
          a⁻¹ ^ (n - k)) := by ring

private lemma catalanExp_odd_weighted_bernoulli_sum (m : ℕ) (hm : 0 < m) :
    ∑ r ∈ Finset.range (m + 1),
        ((2 * m + 1).choose (2 * r + 1) : ℚ) *
          (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
            (4 : ℚ) ^ (2 * r + 1) = 0 := by
  have hplus : (∑ k ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval (1 / 4) * (4 : ℚ) ^ k) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      catalanExp_weighted_bernoulli_add (2 * m + 1) (1 / 4) 4 (by norm_num)]
    norm_num [catalanExp_bernoulli_eval_half_odd]
  have hminus : (∑ k ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval (1 / 4) * (-4 : ℚ) ^ k) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      catalanExp_weighted_bernoulli_add (2 * m + 1) (1 / 4) (-4) (by norm_num)]
    norm_num [catalanExp_bernoulli_eval_zero_odd m hm]
  let f : ℕ → ℚ := fun k => ((2 * m + 1).choose k : ℚ) *
    (Polynomial.bernoulli k).eval (1 / 4) * ((4 : ℚ) ^ k - (-4 : ℚ) ^ k)
  have hdiff : ∑ k ∈ Finset.range (2 * m + 2), f k = 0 := by
    calc
      ∑ k ∈ Finset.range (2 * m + 2), f k =
          (∑ k ∈ Finset.range (2 * m + 2),
            ((2 * m + 1).choose k : ℚ) *
              (Polynomial.bernoulli k).eval (1 / 4) * (4 : ℚ) ^ k) -
          ∑ k ∈ Finset.range (2 * m + 2),
            ((2 * m + 1).choose k : ℚ) *
              (Polynomial.bernoulli k).eval (1 / 4) * (-4 : ℚ) ^ k := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        ring
      _ = 0 := by rw [hplus, hminus, sub_zero]
  rw [catalanExp_sum_range_even_odd f m] at hdiff
  have hpair (r : ℕ) : f (2 * r) + f (2 * r + 1) =
      2 * (((2 * m + 1).choose (2 * r + 1) : ℚ) *
        (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
          (4 : ℚ) ^ (2 * r + 1)) := by
    have heven : Even (2 * r) := ⟨r, by omega⟩
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    dsimp [f]
    rw [neg_pow, heven.neg_one_pow, neg_pow, hodd.neg_one_pow]
    ring
  simp_rw [hpair] at hdiff
  rw [← Finset.mul_sum] at hdiff
  linarith

private noncomputable def catalanExpEulerEvenQ (m : ℕ) : ℚ :=
  -(4 : ℚ) ^ (2 * m + 1) *
      (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) / (2 * m + 1 : ℕ)

private lemma catalanExpEulerEvenQ_zero : catalanExpEulerEvenQ 0 = 1 := by
  norm_num [catalanExpEulerEvenQ, Polynomial.bernoulli_one]

private lemma catalanExpEulerEvenQ_recurrence (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1),
        ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [catalanExpEulerEvenQ_zero]
  · rw [ite_eq_right hm]
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hterm (r : ℕ) : ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
        -(1 / (2 * m + 1 : ℚ)) *
          (((2 * m + 1).choose (2 * r + 1) : ℚ) *
            (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
              (4 : ℚ) ^ (2 * r + 1)) := by
      have hc := Nat.add_one_mul_choose_eq (2 * m) (2 * r)
      have hc' : (2 * m + 1 : ℚ) * (2 * m).choose (2 * r) =
          ((2 * m + 1).choose (2 * r + 1) : ℚ) * (2 * r + 1) := by
        exact_mod_cast hc
      have hratio : ((2 * m).choose (2 * r) : ℚ) / (2 * r + 1 : ℕ) =
          ((2 * m + 1).choose (2 * r + 1) : ℚ) / (2 * m + 1 : ℕ) := by
        apply (div_eq_div_iff (by positivity) (by positivity)).2
        push_cast at hc' ⊢
        nlinarith [hc']
      dsimp [catalanExpEulerEvenQ]
      calc
        ((2 * m).choose (2 * r) : ℚ) *
            (-(4 : ℚ) ^ (2 * r + 1) *
              (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) /
                (2 * r + 1 : ℕ)) =
            -(((2 * m).choose (2 * r) : ℚ) / (2 * r + 1 : ℕ)) *
              ((Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                (4 : ℚ) ^ (2 * r + 1)) := by ring
        _ = -(((2 * m + 1).choose (2 * r + 1) : ℚ) / (2 * m + 1 : ℕ)) *
              ((Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                (4 : ℚ) ^ (2 * r + 1)) := by rw [hratio]
        _ = _ := by
          push_cast
          ring
    calc
      ∑ r ∈ Finset.range (m + 1),
          ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
          -(1 / (2 * m + 1 : ℚ)) *
            ∑ r ∈ Finset.range (m + 1),
              (((2 * m + 1).choose (2 * r + 1) : ℚ) *
                (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                  (4 : ℚ) ^ (2 * r + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r
      _ = 0 := by rw [catalanExp_odd_weighted_bernoulli_sum m hmpos, mul_zero]

private lemma catalanExp_even_binom_sum_reflect (m : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ) * f (m - j) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ) * f j := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using (Finset.mem_range.mp hj)
  rw [show m + 1 - 1 - j = m - j by omega,
    show 2 * (m - j) = 2 * m - 2 * j by omega,
    Nat.choose_symm (by omega : 2 * j ≤ 2 * m),
    show m - (m - j) = j by omega]

private lemma catalanExp_even_E_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) (m : ℕ) :
    (E (2 * m) : ℚ) = catalanExpEulerEvenQ m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
      by_cases hm : m = 0
      · subst m
        rw [mul_zero, hE.1, Int.cast_one, catalanExpEulerEvenQ_zero]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hEraw := hE.2 (2 * m) (by omega)
        have hErawQ : (∑ j ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * j) : ℚ) * (E (2 * m - 2 * j) : ℚ)) = 0 := by
          have hcast := congrArg (fun z : ℤ => (z : ℚ)) hEraw
          push_cast at hcast
          simpa only [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using hcast
        have hEoriented : (∑ r ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * r) : ℚ) * (E (2 * r) : ℚ)) = 0 := by
          rw [← catalanExp_even_binom_sum_reflect m (fun r => (E (2 * r) : ℚ))]
          convert hErawQ using 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [show 2 * m - 2 * j = 2 * (m - j) by omega]
        have hQ := catalanExpEulerEvenQ_recurrence m
        rw [ite_eq_right hm] at hQ
        rw [Finset.sum_range_succ] at hEoriented hQ
        have hprefix : (∑ r ∈ Finset.range m,
            ((2 * m).choose (2 * r) : ℚ) * (E (2 * r) : ℚ)) =
            ∑ r ∈ Finset.range m,
              ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [ih r (Finset.mem_range.mp hr)]
        rw [hprefix] at hEoriented
        simp only [Nat.choose_self, Nat.cast_one, one_mul] at hEoriented hQ
        linarith

private lemma catalanExp_bernoulli_quarter_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) (m : ℕ) :
    (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) =
      -(2 * m + 1 : ℚ) * (E (2 * m) : ℚ) / (4 : ℚ) ^ (2 * m + 1) := by
  have h := catalanExp_even_E_eq E hE m
  rw [catalanExpEulerEvenQ] at h
  have hn : (2 * m + 1 : ℚ) ≠ 0 := by positivity
  have hp : (4 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
  field_simp [hn, hp] at h ⊢
  push_cast at h ⊢
  linear_combination h

-- Extend the even-index sequence by zero at odd indices.
private lemma bernoulli_quarter (k : ℕ) :
    (Polynomial.bernoulli (2 * k + 1)).eval (1 / 4) =
      -(2 * k + 1 : ℚ) * chapter5EulerEven k / 4 ^ (2 * k + 1) := by
  let E (n : ℕ) := if n % 2 = 0 then chapter5EulerEven (n / 2) else 0
  have hE (n : ℕ) (hn : 0 < n) :
      ∑ j ∈ Finset.range (n / 2 + 1), (n.choose (2 * j) : ℤ) * E (n - 2 * j) = 0 := by
    by_cases he : n % 2 = 0
    · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp (Nat.even_iff.mpr he)
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2), ← Finset.sum_range_reflect]
      convert (chapter5EulerEven_recurrence m).trans (ite_eq_right (by omega)) using 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := Finset.mem_range_succ_iff.mp hj
      rw [show m + 1 - 1 - j = m - j by omega,
        show 2 * (m - j) = 2 * m - 2 * j by omega,
        Nat.choose_symm (by omega), show 2 * m - (2 * m - 2 * j) = 2 * j by omega]
      simp [E]
    · apply Finset.sum_eq_zero
      intro j hj
      have hjn : j < n / 2 + 1 := Finset.mem_range.mp hj
      simp [E, show (n - 2 * j) % 2 ≠ 0 by omega]
  simpa [E] using catalanExp_bernoulli_quarter_eq E
    ⟨by simp [E, chapter5EulerEven_zero], hE⟩ k

private noncomputable def term (s n : ℕ) : ℝ := 1 / (n : ℝ) ^ s

private noncomputable def progression (s r : ℕ) : ℝ := ∑' n, term s (4 * n + r)

private lemma summable_progression {s : ℕ} (hs : 1 < s) (r : ℕ) :
    Summable (fun n => term s (4 * n + r)) :=
  (Real.summable_one_div_nat_pow.mpr hs).comp_injective
    (i := fun n : ℕ => 4 * n + r) (by intro a b h; dsimp at h; omega)

private lemma sine_sum {s : ℕ} (hs : 1 < s) :
    HasSum (fun n : ℕ => term s n * Real.sin (2 * Real.pi * n * (1 / 4)))
      (progression s 1 - progression s 3) := by
  let f (n : ℕ) := term s n * Real.sin (2 * Real.pi * n * (1 / 4))
  have h₀ (n : ℕ) : f (2 * n) = 0 := by
    simp only [f, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (2 * n) * (1 / 4) = n * Real.pi by ring, Real.sin_nat_mul_pi,
      mul_zero]
  have h₁ (n : ℕ) : f (2 * (2 * n) + 1) = term s (4 * n + 1) := by
    rw [show 2 * (2 * n) + 1 = 4 * n + 1 by omega]
    simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * Real.pi * (4 * n + 1) * (1 / 4) = Real.pi / 2 + n * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two, mul_one]
  have h₃ (n : ℕ) : f (2 * (2 * n + 1) + 1) = -term s (4 * n + 3) := by
    rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by omega]
    simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (4 * n + 3) * (1 / 4) =
        (Real.pi / 2 + Real.pi) + n * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two, mul_neg_one]
  have ho : HasSum (fun n => f (2 * n + 1)) (progression s 1 + -progression s 3) :=
    HasSum.even_add_odd ((summable_progression hs 1).hasSum.congr_fun h₁)
      ((summable_progression hs 3).hasSum.neg.congr_fun h₃)
  simpa only [zero_add, sub_eq_add_neg] using
    (HasSum.even_add_odd (f := f) (hasSum_zero.congr_fun h₀) ho)

private lemma odd_difference (k : ℕ) (hk : 1 ≤ k) :
    progression (2 * k + 1) 1 - progression (2 * k + 1) 3 =
      Real.pi ^ (2 * k + 1) * (|chapter5EulerEven k| : ℤ) /
        (2 * 2 ^ (2 * k + 1) * (2 * k).factorial) := by
  let s := 2 * k + 1
  have hs : 1 < s := by dsimp [s]; omega
  have hle : progression s 3 ≤ progression s 1 := by
    apply Summable.tsum_le_tsum _ (summable_progression hs 3) (summable_progression hs 1)
    intro n
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : 4 * n + 1 ≤ 4 * n + 3)) s
  have hB : bernoulliFun s (1 / 4) =
      -(s : ℝ) * (chapter5EulerEven k : ℝ) / (4 : ℝ) ^ s := by
    change (Polynomial.map (algebraMap ℚ ℝ) _).eval _ = _
    rw [show (1 / 4 : ℝ) = (algebraMap ℚ ℝ) (1 / 4 : ℚ) by norm_num,
      Polynomial.eval_map_apply, bernoulli_quarter]
    simp [s]
  have h := (sine_sum hs).unique
    (hasSum_one_div_nat_pow_mul_sin (k := k) (by omega)
      (show (1 / 4 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num))
  change progression s 1 - progression s 3 =
    (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ s / 2 / (s.factorial : ℝ) * bernoulliFun s _ at h
  have habs := congrArg abs h
  rw [abs_of_nonneg (sub_nonneg.mpr hle), hB] at habs
  have hval : progression s 1 - progression s 3 =
      (2 * Real.pi) ^ s / 2 / s.factorial *
        (s * |(chapter5EulerEven k : ℝ)| / 4 ^ s) := by
    simpa [abs_mul, abs_div, abs_pow, abs_of_pos Real.pi_pos] using habs
  rw [hval, Int.cast_abs, mul_pow, show (4 : ℝ) ^ s = (2 ^ s) ^ 2 by
    rw [sq, ← mul_pow]; norm_num]
  dsimp only [s]
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

private theorem paperfoldingSeq_even (j : ℕ) :
    paperfoldingSeq (2 * j) = decide (j % 2 = 1) := by
  have h : (2 * j + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_remainder j (by decide)
  rw [Bool.eq_iff_iff]
  simp only [paperfoldingSeq, h, pow_zero, Nat.div_one, decide_eq_true_eq]
  omega

private theorem paperfoldingSeq_odd (j : ℕ) :
    paperfoldingSeq (2 * j + 1) = paperfoldingSeq j := by
  have hj1 : j + 1 ≠ 0 := by omega
  have hmul : (2 * (j + 1)).factorization 2 = (j + 1).factorization 2 + 1 := by
    rw [Nat.factorization_mul (by norm_num) hj1, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
    omega
  have h2j : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
  simp only [paperfoldingSeq, h2j, hmul, pow_add, pow_one]
  rw [show (2 : ℕ) ^ (j + 1).factorization 2 * 2 = 2 * 2 ^ (j + 1).factorization 2 by ring,
    Nat.mul_div_mul_left _ _ (by positivity)]

private noncomputable def pfterm (s n : ℕ) : ℝ :=
  (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ s

private lemma summable_pfterm {s : ℕ} (hs : 1 < s) : Summable (pfterm s) := by
  have hbase : Summable (fun n : ℕ => term s (n + 1)) :=
    (Real.summable_one_div_nat_pow.mpr hs).comp_injective
      (i := fun n : ℕ => n + 1) (by intro a b h; dsimp at h; omega)
  apply Summable.of_norm_bounded hbase
  intro n
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ s := by positivity
  have habs : |2 * ((paperfoldingSeq n).toNat : ℝ) - 1| = 1 := by
    cases paperfoldingSeq n <;> norm_num [Bool.toNat_false, Bool.toNat_true]
  simp only [pfterm, term, Real.norm_eq_abs, abs_div]
  rw [habs, abs_of_pos hpos]

private lemma pfterm_odd (s j : ℕ) :
    pfterm s (2 * j + 1) = (1 / (2 : ℝ) ^ s) * pfterm s j := by
  have h2 : ((2 * j + 1 + 1 : ℕ) : ℝ) = 2 * ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [pfterm, paperfoldingSeq_odd, h2, mul_pow]
  have h1 : ((j + 1 : ℕ) : ℝ) ^ s ≠ 0 := by positivity
  have h2s : (2 : ℝ) ^ s ≠ 0 := by positivity
  field_simp

private lemma pfterm_even_of_even (s t : ℕ) :
    pfterm s (2 * (2 * t)) = -term s (4 * t + 1) := by
  have hf : paperfoldingSeq (2 * (2 * t)) = false := by
    rw [paperfoldingSeq_even]
    simp
  have h41 : 2 * (2 * t) + 1 = 4 * t + 1 := by omega
  simp only [pfterm, term, hf, Bool.toNat_false, Nat.cast_zero, mul_zero, zero_sub, h41,
    neg_div]

private lemma pfterm_even_of_odd (s t : ℕ) :
    pfterm s (2 * (2 * t + 1)) = term s (4 * t + 3) := by
  have hf : paperfoldingSeq (2 * (2 * t + 1)) = true := by
    rw [paperfoldingSeq_even]
    simp [(by omega : (2 * t + 1) % 2 = 1)]
  have h43 : 2 * (2 * t + 1) + 1 = 4 * t + 3 := by omega
  simp only [pfterm, term, hf, Bool.toNat_true, Nat.cast_one, mul_one, h43]
  norm_num

private lemma pfterm_split (s : ℕ) (hs : 1 < s) :
    ∑' n, pfterm s n =
      (progression s 3 - progression s 1) + (1 / (2 : ℝ) ^ s) * ∑' n, pfterm s n := by
  have hS : Summable (pfterm s) := summable_pfterm hs
  have hSeven : Summable (fun j => pfterm s (2 * j)) :=
    hS.comp_injective (i := fun j : ℕ => 2 * j) (by intro a b h; dsimp at h; omega)
  have hSodd : Summable (fun j => pfterm s (2 * j + 1)) :=
    hS.comp_injective (i := fun j : ℕ => 2 * j + 1) (by intro a b h; dsimp at h; omega)
  have hsplit := tsum_even_add_odd hSeven hSodd
  have hodd : (∑' j, pfterm s (2 * j + 1)) = (1 / (2 : ℝ) ^ s) * ∑' n, pfterm s n := by
    calc (∑' j, pfterm s (2 * j + 1)) = ∑' j, (1 / (2 : ℝ) ^ s) * pfterm s j :=
            tsum_congr fun j => pfterm_odd s j
      _ = (1 / (2 : ℝ) ^ s) * ∑' n, pfterm s n := tsum_mul_left
  have heven : (∑' j, pfterm s (2 * j)) = progression s 3 - progression s 1 := by
    have h1 : Summable (fun t => pfterm s (2 * (2 * t))) :=
      hSeven.comp_injective (i := fun t : ℕ => 2 * t) (by intro a b h; dsimp at h; omega)
    have h2 : Summable (fun t => pfterm s (2 * (2 * t + 1))) :=
      hSeven.comp_injective (i := fun t : ℕ => 2 * t + 1) (by intro a b h; dsimp at h; omega)
    have hsplit2 := tsum_even_add_odd (f := fun j => pfterm s (2 * j)) h1 h2
    have e1 : (∑' t, pfterm s (2 * (2 * t))) = -progression s 1 := by
      calc (∑' t, pfterm s (2 * (2 * t))) = ∑' t, -term s (4 * t + 1) :=
              tsum_congr fun t => pfterm_even_of_even s t
        _ = -∑' t, term s (4 * t + 1) := tsum_neg
        _ = -progression s 1 := rfl
    have e2 : (∑' t, pfterm s (2 * (2 * t + 1))) = progression s 3 := by
      calc (∑' t, pfterm s (2 * (2 * t + 1))) = ∑' t, term s (4 * t + 3) :=
              tsum_congr fun t => pfterm_even_of_odd s t
        _ = progression s 3 := rfl
    rw [e1, e2] at hsplit2
    linarith [hsplit2]
  rw [heven, hodd] at hsplit
  exact hsplit.symm

end tsum_paperfolding_two_mul_add_one

open tsum_paperfolding_two_mul_add_one

/-- **A paperfolding Dirichlet series at odd integers.** Let $(f_n)_{n \ge 0}$ be the regular
paperfolding sequence, indexed from $0$, and let $E_{2k}$ be the even-index Euler number. For
every integer $k \ge 1$,
$$
(2^{4k+1} - 2^{2k}) \sum_{n \ge 0} \frac{2 f_n - 1}{(n+1)^{2k+1}}
= -\frac{2^{2k-1} \pi^{2k+1} |E_{2k}|}{(2k)!}.
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$, the sum is
$\sum_{n \ge 1} (2 b_n - 1)/n^{2k+1}$.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 5 (`jis-2025-25.4.4-lem-5`);
`bₙ` read from arXiv:2508.04151v1. -/
public theorem tsum_paperfolding_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) *
        ∑' n : ℕ, (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) =
      -((2 : ℝ) ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ (2 * k + 1) *
        ((|chapter5EulerEven k| : ℤ) : ℝ) := by
  let s := 2 * k + 1
  have hs : 1 < s := by dsimp [s]; omega
  have hsplit := pfterm_split s hs
  have hdiff := odd_difference k hk
  change progression s 1 - progression s 3 = _ at hdiff
  change ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) * ∑' n, pfterm s n =
    -((2 : ℝ) ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ s *
      ((|chapter5EulerEven k| : ℤ) : ℝ)
  have h2s0 : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hkey : ((2 : ℝ) ^ s - 1) * ∑' n, pfterm s n
      = (2 : ℝ) ^ s * (progression s 3 - progression s 1) := by
    field_simp at hsplit ⊢
    linear_combination hsplit
  have hC : ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k))
      = 2 ^ (2 * k) * ((2 : ℝ) ^ s - 1) := by
    have hs_eq : s = 2 * k + 1 := rfl
    rw [hs_eq, show 4 * k + 1 = 2 * k + (2 * k + 1) by omega, pow_add]
    ring
  have hD : progression s 3 - progression s 1
      = -(progression s 1 - progression s 3) := by ring
  have hpred : (2 : ℝ) ^ (2 * k - 1) * 2 = 2 ^ (2 * k) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  conv_lhs => rw [hC, mul_assoc, hkey, hD, hdiff]
  dsimp only [s]
  simp only [pow_succ (2 : ℝ) (2 * k)]
  rw [← hpred]
  field_simp

end MetaMathlibExt
