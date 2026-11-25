/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import MathlibExt.NumberTheory.OeisA265233
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The generating function of A265233

`tsum_a265233_eq` proves that for every real number `x` with `|x| < 1/12` and
`|27x(1 - 4x)^2| < 1`, the generating function `∑ a_n x^n` of the sequence `a265233` equals
`(₂F₁(1/3, 2/3; 1; 27x(1 - 4x)^2) + 5) / 6`.

The identity is stated on the common convergence domain `|x| < 1/12` and `|27x(1 - 4x)^2| < 1`
(Mathlib's `₂F₁` takes the junk value `0` outside its radius of convergence).

## Proof

Let `c_k = (3k)! / (k!)^3`, which is `27^k` times the `k`-th coefficient of
`₂F₁(1/3, 2/3; 1; ·)`, and let `t(n, k) = c_k C(2k, n - k) (-4)^(n - k)` for `k ≤ n` and
`t(n, k) = 0` for `k > n`. Then `d_n = ∑_k t(n, k)` is the coefficient of `x^n` in
`∑_k c_k (x(1 - 4x)^2)^k`.

* With the certificate `G(n, k) = -n k t(n, k)`, every `k` satisfies
  `n² t(n, k) - (19n² - 19n + 6) t(n - 1, k) + 96 (n - 1)² t(n - 2, k)
  - 144 (n - 1)(n - 2) t(n - 3, k) = G(n, k + 1) - G(n, k)`.
  Summing over `k` shows that `d_n` satisfies the recurrence that defines `a265233`, so
  `6 a_n = d_n` for `n ≥ 1`, while `d_0 = 1 = a_0`.
* For `|x| < 1/100` the double series `∑_{k, j} c_k C(2k, j) (-4)^j x^(k + j)` converges
  absolutely. Summing it by antidiagonals and by rows proves the identity near `0`.
* The explicit Franel formula `a265233_eq_sum_franel` gives `0 ≤ a_n ≤ 12^n`, so the left side
  is a power series of radius at least `1/12`. The right side is analytic wherever
  `|27x(1 - 4x)^2| < 1`. Every point between `0` and `x` satisfies both bounds, and the identity
  theorem extends the equality along that interval.
-/

set_option autoImplicit false

@[expose] public section

open Finset

namespace MathlibExt.NumberTheory.OeisA265233Wanted

/-! ### The coefficients of `₂F₁(1/3, 2/3; 1; ·)` -/

/-- The `k`-th coefficient of the hypergeometric series `₂F₁(1/3, 2/3; 1; ·)`. -/
private noncomputable abbrev hypCoeff (k : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient (1 / 3 : ℝ) (2 / 3 : ℝ) 1 k

private theorem hypCoeff_zero : hypCoeff 0 = 1 := by
  simp [hypCoeff, ordinaryHypergeometricCoefficient]

private theorem hypCoeff_succ (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * hypCoeff (k + 1) = (1 / 3 + k) * (2 / 3 + k) * hypCoeff k := by
  simp only [hypCoeff, ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval,
    ascPochhammer_eval_one, Nat.factorial_succ]
  push_cast
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem hypCoeff_pos_le_one (k : ℕ) : 0 < hypCoeff k ∧ hypCoeff k ≤ 1 := by
  induction k with
  | zero => simp [hypCoeff_zero]
  | succ k ih =>
    have h := hypCoeff_succ k
    have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    obtain ⟨h0, h1⟩ := ih
    constructor
    · have : 0 < ((k : ℝ) + 1) ^ 2 * hypCoeff (k + 1) := by rw [h]; positivity
      exact pos_of_mul_pos_right this hk.le
    · have : ((k : ℝ) + 1) ^ 2 * hypCoeff (k + 1) ≤ ((k : ℝ) + 1) ^ 2 * 1 := by
        rw [h]
        have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
        nlinarith
      exact le_of_mul_le_mul_left this hk

/-- The multinomial coefficient `(3k)! / (k!)^3`, written as `27^k` times `hypCoeff k`. -/
private noncomputable def multinom (k : ℕ) : ℝ := hypCoeff k * 27 ^ k

private theorem multinom_succ (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * multinom (k + 1) = 3 * (3 * k + 1) * (3 * k + 2) * multinom k := by
  have := hypCoeff_succ k
  simp only [multinom, pow_succ]
  linear_combination (27 : ℝ) ^ k * 27 * this

private theorem multinom_pos (k : ℕ) : 0 < multinom k := by
  have := (hypCoeff_pos_le_one k).1
  unfold multinom
  positivity

private theorem multinom_zero : multinom 0 = 1 := by simp [multinom, hypCoeff_zero]

private theorem multinom_one : multinom 1 = 6 := by
  have := multinom_succ 0
  norm_num [multinom_zero] at this
  linarith

private theorem multinom_two : multinom 2 = 90 := by
  have := multinom_succ 1
  norm_num [multinom_one] at this
  linarith

private theorem multinom_three : multinom 3 = 1680 := by
  have := multinom_succ 2
  norm_num [multinom_two] at this
  linarith

/-! ### The coefficients of `₂F₁(1/3, 2/3; 1; 27x(1 - 4x)^2)` -/

/-- The coefficient `c_k C(2k, j) (-4)^j` of `x^(k + j)` in `c_k (x(1 - 4x)^2)^k`. -/
private noncomputable def term (k j : ℕ) : ℝ := multinom k * ((2 * k).choose j : ℝ) * (-4) ^ j

/-- The summand `term k (n - k)` of the `n`-th coefficient, extended by `0` for `k > n`. -/
private noncomputable def termAt (n k : ℕ) : ℝ := if k ≤ n then term k (n - k) else 0

/-- The coefficient of `x^n` in `∑_k c_k (x(1 - 4x)^2)^k`. -/
private noncomputable def coeffSum (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), term k (n - k)

private theorem termAt_of_eq {n k j : ℕ} (h : n = k + j) : termAt n k = term k j := by
  subst h
  simp [termAt]

private theorem termAt_of_lt {n k : ℕ} (h : n < k) : termAt n k = 0 := by
  simp [termAt, Nat.not_le.mpr h]

private theorem coeffSum_eq_sum_termAt (n M : ℕ) (hM : n + 1 ≤ M) :
    coeffSum n = ∑ k ∈ range M, termAt n k := by
  rw [coeffSum, ← Finset.sum_subset (Finset.range_mono hM)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [termAt_of_eq (by have := Finset.mem_range.mp hk; omega : n = k + (n - k))]
  · intro k _ hk
    exact termAt_of_lt (by simpa using hk)

private theorem choose_rel (N j : ℕ) :
    ((j : ℝ) + 1) * (N.choose (j + 1) : ℝ) = ((N : ℝ) - j) * (N.choose j : ℝ) := by
  rcases le_or_gt j N with h | h
  · have h' : ((N.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((N.choose j * (N - j) : ℕ) : ℝ) := by
      rw [Nat.choose_succ_right_eq N j]
    push_cast [Nat.cast_sub h] at h'
    linear_combination h'
  · simp [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : N < j + 1)]

private theorem choose_two_rel (k j : ℕ) :
    ((2 * (k + 1)).choose (j + 2) : ℝ) =
      (2 * k).choose (j + 2) + 2 * (2 * k).choose (j + 1) + (2 * k).choose j := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.choose_succ_succ, Nat.choose_succ_succ,
    Nat.choose_succ_succ (2 * k) (j + 1)]
  push_cast
  ring

/-- The telescoping certificate `G(m + 3, k) = -(m + 3) k t(m + 3, k)`. -/
private noncomputable def certificate (m k : ℕ) : ℝ := -((m : ℝ) + 3) * k * termAt (m + 3) k

-- The recurrence operator of `a265233` applied to `t(·, k)` telescopes in `k`.
private theorem termAt_step (m k : ℕ) :
    ((m : ℝ) + 3) ^ 2 * termAt (m + 3) k
      - (19 * ((m : ℝ) + 3) ^ 2 - 19 * ((m : ℝ) + 3) + 6) * termAt (m + 2) k
      + 96 * ((m : ℝ) + 2) ^ 2 * termAt (m + 1) k
      - 144 * ((m : ℝ) + 2) * ((m : ℝ) + 1) * termAt m k
      = certificate m (k + 1) - certificate m k := by
  rcases le_or_gt k m with hkm | hkm
  · -- All four summands are in range: write `m = k + a`.
    obtain ⟨a, rfl⟩ : ∃ a, m = k + a := ⟨m - k, by omega⟩
    rw [certificate, certificate, termAt_of_eq (show k + a + 3 = k + (a + 2 + 1) by ring),
      termAt_of_eq (show k + a + 2 = k + (a + 2) by ring),
      termAt_of_eq (show k + a + 1 = k + (a + 1) by ring),
      termAt_of_eq (show k + a = k + a from rfl),
      termAt_of_eq (show k + a + 3 = (k + 1) + (a + 2) by ring)]
    unfold term
    have hH := multinom_succ k
    have h4 := choose_two_rel k a
    have h3 := choose_rel (2 * k) (a + 2)
    have h2 := choose_rel (2 * k) (a + 1)
    have h1 := choose_rel (2 * k) a
    push_cast at hH h4 h3 h2 h1 ⊢
    refine mul_left_cancel₀ (by positivity : ((k : ℝ) + 1) ≠ 0) ?_
    set H := multinom k
    set q : ℝ := (-4) ^ a
    linear_combination
      16 * ((k : ℝ) + a + 3) * q * ((2 * (k + 1)).choose (a + 2) : ℝ) * hH
      + 48 * ((k : ℝ) + a + 3) * (3 * k + 1) * (3 * k + 2) * H * q * h4
      - 64 * ((k : ℝ) + a + 3) * (k + 1) * H * q * h3
      - 48 * H * q * (5 * k ^ 2 + 5 * k * a + 20 * k + 5 * a + 13) * h2
      - 48 * H * q * (3 * k ^ 2 + 3 * k * a + 12 * k + 3 * a + 7) * h1
  · -- The boundary summands: write `k = m + 1 + d`.
    obtain ⟨d, rfl⟩ : ∃ d, k = m + 1 + d := ⟨k - (m + 1), by omega⟩
    match d with
    | 0 =>
      rw [certificate, certificate, termAt_of_eq (show m + 3 = m + 1 + 0 + 2 by ring),
        termAt_of_eq (show m + 2 = m + 1 + 0 + 1 by ring),
        termAt_of_eq (show m + 1 = m + 1 + 0 + 0 by ring),
        termAt_of_lt (show m < m + 1 + 0 by omega),
        termAt_of_eq (show m + 3 = m + 1 + 0 + 1 + 1 by ring)]
      unfold term
      have hH := multinom_succ (m + 1)
      have h3 := choose_rel (2 * (m + 1)) 1
      simp only [Nat.choose_zero_right, Nat.choose_one_right, add_zero] at hH h3 ⊢
      push_cast at hH h3 ⊢
      linear_combination -8 * ((m : ℝ) + 3) * hH + 16 * ((m : ℝ) + 3) * multinom (m + 1) * h3
    | 1 =>
      rw [certificate, certificate, termAt_of_eq (show m + 3 = m + 1 + 1 + 1 by ring),
        termAt_of_eq (show m + 2 = m + 1 + 1 + 0 by ring),
        termAt_of_lt (show m + 1 < m + 1 + 1 by omega),
        termAt_of_lt (show m < m + 1 + 1 by omega),
        termAt_of_eq (show m + 3 = m + 1 + 1 + 1 + 0 by ring)]
      unfold term
      have hH := multinom_succ (m + 2)
      simp only [Nat.choose_zero_right, Nat.choose_one_right] at hH ⊢
      push_cast at hH ⊢
      linear_combination hH
    | 2 =>
      rw [certificate, certificate, termAt_of_eq (show m + 3 = m + 1 + 2 + 0 by ring),
        termAt_of_lt (show m + 2 < m + 1 + 2 by omega),
        termAt_of_lt (show m + 1 < m + 1 + 2 by omega),
        termAt_of_lt (show m < m + 1 + 2 by omega),
        termAt_of_lt (show m + 3 < m + 1 + 2 + 1 by omega)]
      unfold term
      simp only [Nat.choose_zero_right]
      push_cast
      ring
    | d + 3 =>
      rw [certificate, certificate, termAt_of_lt (show m + 3 < m + 1 + (d + 3) by omega),
        termAt_of_lt (show m + 2 < m + 1 + (d + 3) by omega),
        termAt_of_lt (show m + 1 < m + 1 + (d + 3) by omega),
        termAt_of_lt (show m < m + 1 + (d + 3) by omega),
        termAt_of_lt (show m + 3 < m + 1 + (d + 3) + 1 by omega)]
      ring

private theorem coeffSum_recurrence (m : ℕ) :
    ((m : ℝ) + 3) ^ 2 * coeffSum (m + 3) =
      (19 * ((m : ℝ) + 3) ^ 2 - 19 * ((m : ℝ) + 3) + 6) * coeffSum (m + 2)
      - 96 * ((m : ℝ) + 2) ^ 2 * coeffSum (m + 1)
      + 144 * ((m : ℝ) + 2) * ((m : ℝ) + 1) * coeffSum m := by
  have hsum := Finset.sum_congr rfl (fun k (_ : k ∈ range (m + 4)) => termAt_step m k)
  rw [Finset.sum_range_sub] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← coeffSum_eq_sum_termAt (m + 3) (m + 4) le_rfl,
    ← coeffSum_eq_sum_termAt (m + 2) (m + 4) (by omega),
    ← coeffSum_eq_sum_termAt (m + 1) (m + 4) (by omega),
    ← coeffSum_eq_sum_termAt m (m + 4) (by omega)] at hsum
  have h0 : certificate m (m + 4) = 0 := by rw [certificate, termAt_of_lt (by omega)]; ring
  have h1 : certificate m 0 = 0 := by simp [certificate]
  rw [h0, h1] at hsum
  linear_combination hsum

private theorem coeffSum_zero : coeffSum 0 = 1 := by
  simp [coeffSum, term, multinom_zero]

private theorem coeffSum_one : coeffSum 1 = 6 := by
  simp [coeffSum, term, Finset.sum_range_succ, multinom_zero, multinom_one]

private theorem coeffSum_two : coeffSum 2 = 42 := by
  simp [coeffSum, term, Finset.sum_range_succ, multinom_zero, multinom_one, multinom_two]
  norm_num

private theorem coeffSum_three : coeffSum 3 = 336 := by
  simp [coeffSum, term, Finset.sum_range_succ, multinom_zero, multinom_one, multinom_two,
    multinom_three]
  norm_num

private theorem a265233_eq_coeffSum (n : ℕ) (hn : 1 ≤ n) :
    (a265233 n : ℝ) = coeffSum n / 6 := by
  induction n using a265233.induct with
  | case1 => omega
  | case2 => rw [coeffSum_one]; norm_num [a265233]
  | case3 => rw [coeffSum_two]; norm_num [a265233]
  | case4 => rw [coeffSum_three]; norm_num [a265233]
  | case5 n ih₃ ih₂ ih₁ =>
    rw [a265233]
    push_cast
    rw [ih₃ (by omega), ih₂ (by omega), ih₁ (by omega)]
    have h := coeffSum_recurrence (n + 1)
    rw [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl,
      show n + 1 + 1 = n + 2 from rfl] at h
    rw [show n.succ.succ.succ.succ = n + 4 from rfl]
    push_cast at h
    rw [div_eq_iff (by positivity)]
    linear_combination (-1 / 6 : ℝ) * h

/-! ### The identity near `0` -/

-- The row sums of the double series, for a general weight `w`.
private theorem hasSum_row (k : ℕ) (w y : ℝ) :
    HasSum (fun j : ℕ => multinom k * ((2 * k).choose j : ℝ) * w ^ j * y ^ (k + j))
      (hypCoeff k * (27 * y * (1 + w * y) ^ 2) ^ k) := by
  have hzero : ∀ j ∉ range (2 * k + 1),
      multinom k * ((2 * k).choose j : ℝ) * w ^ j * y ^ (k + j) = 0 := by
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp
  have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hzero
  convert hfin using 1
  have e : (27 * y * (1 + w * y) ^ 2) ^ k = 27 ^ k * y ^ k * (w * y + 1) ^ (2 * k) := by
    rw [mul_pow, mul_pow, ← pow_mul, add_comm]
  rw [e, add_pow, multinom, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The terms `c_k C(2k, j) (-4)^j x^(k + j)` of the double series. -/
private noncomputable def doubleTerm (x : ℝ) (p : ℕ × ℕ) : ℝ := term p.1 p.2 * x ^ (p.1 + p.2)

private theorem norm_doubleTerm (x : ℝ) (p : ℕ × ℕ) :
    ‖doubleTerm x p‖ =
      multinom p.1 * ((2 * p.1).choose p.2 : ℝ) * 4 ^ p.2 * |x| ^ (p.1 + p.2) := by
  rw [doubleTerm, term, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
    abs_of_pos (multinom_pos _), Nat.abs_cast]
  norm_num

private theorem summable_norm_doubleTerm (x : ℝ) (hx : 27 * |x| * (1 + 4 * |x|) ^ 2 < 1) :
    Summable (fun p => ‖doubleTerm x p‖) := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  simp only [norm_doubleTerm]
  refine ⟨fun k => (hasSum_row k 4 |x|).summable, ?_⟩
  simp only [fun k => (hasSum_row k 4 |x|).tsum_eq]
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity) hx)
  · have := (hypCoeff_pos_le_one k).1
    positivity
  · have := hypCoeff_pos_le_one k
    have h0 : 0 ≤ (27 * |x| * (1 + 4 * |x|) ^ 2) ^ k := by positivity
    calc hypCoeff k * (27 * |x| * (1 + 4 * |x|) ^ 2) ^ k
        ≤ 1 * (27 * |x| * (1 + 4 * |x|) ^ 2) ^ k := by gcongr; exact this.2
      _ = _ := one_mul _

private theorem sum_antidiagonal_doubleTerm (x : ℝ) (n : ℕ) :
    ∑ p ∈ antidiagonal n, doubleTerm x p = coeffSum n * x ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeffSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [doubleTerm, Nat.add_sub_cancel' hk']

private theorem hasSum_coeffSum (x : ℝ) (hx : 27 * |x| * (1 + 4 * |x|) ^ 2 < 1) :
    HasSum (fun n => coeffSum n * x ^ n)
      (∑' k, hypCoeff k * (27 * x * (1 - 4 * x) ^ 2) ^ k) := by
  have hT : Summable (doubleTerm x) := (summable_norm_doubleTerm x hx).of_norm
  set e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hsig : Summable (fun c => doubleTerm x (e c)) := e.summable_iff.mpr hT
  have hrow : ∀ n : ℕ, Summable fun c : antidiagonal n => doubleTerm x (e ⟨n, c⟩) :=
    fun n => (hasSum_fintype _).summable
  have hinner : ∀ n, ∑' c : antidiagonal n, doubleTerm x (e ⟨n, c⟩) = coeffSum n * x ^ n := by
    intro n
    rw [tsum_fintype, ← sum_antidiagonal_doubleTerm x n]
    exact Finset.sum_coe_sort (antidiagonal n) (doubleTerm x)
  have hsum : Summable fun n => coeffSum n * x ^ n := by
    simpa only [hinner] using hsig.sigma' hrow
  refine hsum.hasSum_iff.mpr ?_
  have hrows : ∑' p, doubleTerm x p = ∑' k, hypCoeff k * (27 * x * (1 - 4 * x) ^ 2) ^ k := by
    rw [hT.tsum_prod' (fun k => ?_)]
    · refine tsum_congr fun k => ?_
      have := (hasSum_row k (-4) x).tsum_eq
      simp only [doubleTerm, term]
      rw [show (1 + -4 * x) = 1 - 4 * x by ring] at this
      rw [← this]
    · exact (hasSum_row k (-4) x).summable.congr fun j => by simp [doubleTerm, term]
  rw [← hrows, ← e.tsum_eq, hsig.tsum_sigma' hrow]
  exact tsum_congr fun n => (hinner n).symm

private theorem ordinaryHypergeometric_eq_tsum_hypCoeff (z : ℝ) :
    ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1 z = ∑' k, hypCoeff k * z ^ k := by
  rw [ordinaryHypergeometric_eq_tsum]
  rfl

private theorem a265233_mul_pow (x : ℝ) (n : ℕ) :
    (a265233 n : ℝ) * x ^ n = coeffSum n * x ^ n / 6 + (if n = 0 then 5 / 6 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coeffSum_zero, a265233]
    norm_num
  · rw [a265233_eq_coeffSum n hn]
    simp [show n ≠ 0 by omega]
    ring

private theorem tsum_a265233_eq_of_small (x : ℝ) (hx : 27 * |x| * (1 + 4 * |x|) ^ 2 < 1) :
    ∑' n : ℕ, (a265233 n : ℝ) * x ^ n =
      (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1 (27 * x * (1 - 4 * x) ^ 2) + 5) / 6 := by
  have h := ((hasSum_coeffSum x hx).div_const 6).add (hasSum_ite_eq 0 (5 / 6 : ℝ))
  calc ∑' n : ℕ, (a265233 n : ℝ) * x ^ n
      = ∑' n : ℕ, (coeffSum n * x ^ n / 6 + if n = 0 then (5 / 6 : ℝ) else 0) :=
        tsum_congr (a265233_mul_pow x)
    _ = (∑' k, hypCoeff k * (27 * x * (1 - 4 * x) ^ 2) ^ k) / 6 + 5 / 6 := h.tsum_eq
    _ = _ := by rw [ordinaryHypergeometric_eq_tsum_hypCoeff]; ring

/-! ### Analyticity of both sides -/

private theorem franel_le (m : ℕ) : MetaMathlibExt.binomialPowerSeq 3 0 m ≤ 8 ^ m := by
  unfold MetaMathlibExt.binomialPowerSeq
  calc ∑ k ∈ range (m + 1), m.choose k ^ 3 * (m + k).choose k ^ 0
      ≤ ∑ k ∈ range (m + 1), m.choose k * 4 ^ m := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h2 : m.choose k ^ 2 ≤ 4 ^ m := by
          calc m.choose k ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (Nat.choose_le_two_pow m k) 2
            _ = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        calc m.choose k ^ 3 * (m + k).choose k ^ 0 = m.choose k * m.choose k ^ 2 := by ring
          _ ≤ m.choose k * 4 ^ m := Nat.mul_le_mul_left _ h2
    _ = 2 ^ m * 4 ^ m := by rw [← Finset.sum_mul, Nat.sum_range_choose]
    _ = 8 ^ m := by rw [← mul_pow]; norm_num

private theorem abs_a265233_le (n : ℕ) : |(a265233 n : ℝ)| ≤ 12 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a265233]
  · rw [a265233_eq_sum_franel n hn]
    push_cast
    have hle : ∑ m ∈ range (n + 1), (n.choose m : ℝ) * 4 ^ (n - m) *
        (MetaMathlibExt.binomialPowerSeq 3 0 m : ℝ) ≤
          ∑ m ∈ range (n + 1), (n.choose m : ℝ) * 4 ^ (n - m) * 8 ^ m := by
      refine Finset.sum_le_sum fun m _ => ?_
      gcongr
      exact_mod_cast franel_le m
    have hsum : ∑ m ∈ range (n + 1), (n.choose m : ℝ) * 4 ^ (n - m) * 8 ^ m = 12 ^ n := by
      rw [show (12 : ℝ) = 8 + 4 by norm_num, add_pow]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hnn : 0 ≤ ∑ m ∈ range (n + 1), (n.choose m : ℝ) * 4 ^ (n - m) *
        (MetaMathlibExt.binomialPowerSeq 3 0 m : ℝ) :=
      Finset.sum_nonneg fun m _ => by positivity
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hnn)]
    have h12 : (0 : ℝ) ≤ 12 ^ n := by positivity
    linarith

/-- The power series `∑ a_n x^n`. -/
private noncomputable def a265233Series : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => (a265233 n : ℝ))

private theorem le_radius_a265233Series :
    (((12 : NNReal)⁻¹ : NNReal) : ENNReal) ≤ a265233Series.radius := by
  refine a265233Series.le_radius_of_bound 1 fun n => ?_
  rw [a265233Series, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
  push_cast
  calc |(a265233 n : ℝ)| * 12⁻¹ ^ n ≤ 12 ^ n * 12⁻¹ ^ n := by
        gcongr
        exact abs_a265233_le n
    _ = 1 := by rw [← mul_pow]; norm_num

private theorem analyticAt_tsum_a265233 (y : ℝ) (hy : |y| < 1 / 12) :
    AnalyticAt ℝ (fun y : ℝ => ∑' n : ℕ, (a265233 n : ℝ) * y ^ n) y := by
  have hpos : 0 < a265233Series.radius := lt_of_lt_of_le (by simp) le_radius_a265233Series
  have h := (a265233Series.hasFPowerSeriesOnBall hpos).mono (by simp) le_radius_a265233Series
  have hfun : (fun y : ℝ => ∑' n : ℕ, (a265233 n : ℝ) * y ^ n) = a265233Series.sum := by
    funext y
    exact (FormalMultilinearSeries.ofScalars_sum_eq (fun n => (a265233 n : ℝ)) y).symm
  rw [hfun]
  apply h.analyticAt_of_mem
  rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  push_cast
  linarith

private theorem analyticAt_ordinaryHypergeometric (y : ℝ)
    (hy : |27 * y * (1 - 4 * y) ^ 2| < 1) :
    AnalyticAt ℝ (fun y : ℝ => (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
      (27 * y * (1 - 4 * y) ^ 2) + 5) / 6) y := by
  set p := ordinaryHypergeometricSeries ℝ (1 / 3 : ℝ) (2 / 3 : ℝ) 1
  have habc : ∀ kn : ℕ, (kn : ℝ) ≠ -(1 / 3) ∧ (kn : ℝ) ≠ -(2 / 3) ∧ (kn : ℝ) ≠ -1 := by
    intro kn
    have := kn.cast_nonneg (α := ℝ)
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith
  have hr : p.radius = 1 := ordinaryHypergeometricSeries_radius_eq_one ℝ _ _ _ habc
  have h := p.hasFPowerSeriesOnBall (by rw [hr]; exact one_pos)
  rw [hr] at h
  have hF : AnalyticAt ℝ p.sum (27 * y * (1 - 4 * y) ^ 2) := by
    apply h.analyticAt_of_mem
    rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp, Metric.eball_coe, Metric.mem_ball,
      dist_zero_right, Real.norm_eq_abs]
    simpa using hy
  have hz : AnalyticAt ℝ (fun y : ℝ => 27 * y * (1 - 4 * y) ^ 2) y := by fun_prop
  exact ((AnalyticAt.comp (f := fun y : ℝ => 27 * y * (1 - 4 * y) ^ 2) hF hz).add
    analyticAt_const).div_const

/-! ### The generating function -/

/-- **Generating function of A265233.** Let $(a_n)_{n \ge 0}$ be the sequence A265233 and let
${}_2F_1$ be the Gauss hypergeometric function. For every real number $x$ with $|x| < 1/12$ and
$|27x(1 - 4x)^2| < 1$,

$$\sum_{n \ge 0} a_n x^n = \frac{{}_2F_1\bigl(\tfrac13, \tfrac23; 1; 27x(1 - 4x)^2\bigr) + 5}{6}.$$

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Corollary 2. -/
theorem tsum_a265233_eq (x : ℝ) (hx : |x| < 1 / 12)
    (hz : |27 * x * (1 - 4 * x) ^ 2| < 1) :
    ∑' n : ℕ, (a265233 n : ℝ) * x ^ n =
      (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
        (27 * x * (1 - 4 * x) ^ 2) + 5) / 6 := by
  -- Every point between `0` and `x` lies in the domain of both sides.
  have hU : ∀ y ∈ Set.uIcc 0 x, |y| < 1 / 12 ∧ |27 * y * (1 - 4 * y) ^ 2| < 1 := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hx' : x < 1 / 12 := lt_of_le_of_lt (le_abs_self x) hx
      refine ⟨by rw [abs_of_nonneg h0]; linarith, ?_⟩
      rw [abs_of_nonneg (by positivity)]
      -- `1 - 27y(1 - 4y)^2 = (1 - 12y)^2 (1 - 3y)`
      have hpos : 0 < (1 - 12 * y) ^ 2 * (1 - 3 * y) :=
        mul_pos (pow_pos (by linarith) 2) (by linarith)
      nlinarith
    · have hx' : -x < 1 / 12 := lt_of_le_of_lt (neg_le_abs x) hx
      refine ⟨by rw [abs_of_nonpos h1]; linarith, ?_⟩
      have h2 : (1 - 4 * y) ^ 2 ≤ (1 - 4 * x) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h3 : (-y) * (1 - 4 * y) ^ 2 ≤ (-x) * (1 - 4 * x) ^ 2 :=
        mul_le_mul (by linarith) h2 (by positivity) (by linarith)
      have hzy : |27 * y * (1 - 4 * y) ^ 2| = 27 * ((-y) * (1 - 4 * y) ^ 2) := by
        rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
        ring
      have hzx : |27 * x * (1 - 4 * x) ^ 2| = 27 * ((-x) * (1 - 4 * x) ^ 2) := by
        rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
        ring
      rw [hzy]
      rw [hzx] at hz
      linarith
  have hf : AnalyticOnNhd ℝ (fun y : ℝ => ∑' n : ℕ, (a265233 n : ℝ) * y ^ n) (Set.uIcc 0 x) :=
    fun y hy => analyticAt_tsum_a265233 y (hU y hy).1
  have hg : AnalyticOnNhd ℝ (fun y : ℝ => (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
      (27 * y * (1 - 4 * y) ^ 2) + 5) / 6) (Set.uIcc 0 x) :=
    fun y hy => analyticAt_ordinaryHypergeometric y (hU y hy).2
  have hfg : (fun y : ℝ => ∑' n : ℕ, (a265233 n : ℝ) * y ^ n) =ᶠ[nhds 0]
      (fun y : ℝ => (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
        (27 * y * (1 - 4 * y) ^ 2) + 5) / 6) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 100)] with y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    apply tsum_a265233_eq_of_small
    have ht : 0 ≤ |y| := abs_nonneg y
    have h1 : (1 + 4 * |y|) ^ 2 ≤ 2 := by nlinarith
    calc 27 * |y| * (1 + 4 * |y|) ^ 2 ≤ 27 * |y| * 2 := by gcongr
      _ < 1 := by linarith
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_uIcc Set.left_mem_uIcc hfg
    Set.right_mem_uIcc

end MathlibExt.NumberTheory.OeisA265233Wanted
