/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Tactic.LinearCombination

/-!
# Best approximations by continued-fraction convergents

Consecutive continuants form an integer basis. In this basis the exact value of the continued
fraction relates the two approximation errors by the complete quotient.
-/

namespace MetaMathlibExt

open GenContFract
open GenContFract (of)

/-- Express an integer pair in the basis of the current and preceding continuants. -/
private theorem exists_continuant_coefficients {x : ℝ}
    (hinf : ∀ k, ¬(of x).TerminatedAt k) (p q : ℤ) (n : ℕ) :
    ∃ a b : ℤ,
      (p : ℝ) = a * ((of x).contsAux (n + 1)).a + b * ((of x).contsAux n).a ∧
      (q : ℝ) = a * ((of x).contsAux (n + 1)).b + b * ((of x).contsAux n).b := by
  induction n with
  | zero =>
    refine ⟨q, p - q * ⌊x⌋, ?_⟩
    simp [of_h_eq_floor]
  | succ n ih =>
    obtain ⟨a, b, hp, hq⟩ := ih
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp (hinf n)
    obtain ⟨h₁, z, hz⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hgp
    refine ⟨b, a - b * z, ?_⟩
    rw [contsAux_recurrence hgp rfl rfl, h₁, hz, Int.cast_sub, Int.cast_mul]
    constructor
    · rw [hp]
      ring
    · rw [hq]
      ring

/-- The denominator bound forces the two coefficients to have opposite weak signs.
The nonzero coefficient of the preceding continuant then gives strict improvement. -/
private theorem one_lt_abs_coeff_sub_mul {a b : ℤ} {Q R t : ℝ} (hQ : 0 < Q) (hR : 0 < R)
    (hpos : 0 < a * Q + b * R) (hle : a * Q + b * R ≤ Q) (hb : b ≠ 0) (ht : 1 < t) :
    1 < |(a : ℝ) - b * t| := by
  have ht₀ : 0 ≤ t := zero_le_one.trans ht.le
  rcases lt_or_gt_of_ne hb with hb | hb
  · have hb' : (b : ℝ) ≤ -1 := by exact_mod_cast (show b ≤ -1 by omega)
    have ha : 0 < (a : ℝ) := by
      by_contra! h
      linarith [mul_nonpos_of_nonpos_of_nonneg h hQ.le,
        mul_nonpos_of_nonpos_of_nonneg (le_trans hb' (by norm_num)) hR.le]
    calc
      1 < (a : ℝ) - b * t := by linarith [mul_le_mul_of_nonneg_right hb' ht₀]
      _ ≤ _ := le_abs_self _
  · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have ha : a ≤ 0 := by
      by_contra! h
      have ha' : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
      linarith [mul_le_mul_of_nonneg_right ha' hQ.le, mul_le_mul_of_nonneg_right hb' hR.le]
    have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
    calc
      1 < -((a : ℝ) - b * t) := by linarith [mul_le_mul_of_nonneg_right hb' ht₀]
      _ ≤ _ := neg_le_abs _

/-- **Convergents minimize $|p - qx|$ up to their denominator.** Let $x$ be an irrational real
number with continued fraction convergents $p_k / q_k$, where $p_0 / q_0 = \lfloor x \rfloor / 1$.
If $n > 1$ is a natural number and $p, q$ are integers with $0 < q \le q_n$ and
$p / q \ne p_n / q_n$, then $|p_n - q_n x| < |p - q x|$.

This is Theorem 182 of Hardy and Wright.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 10
(`integers-2025-A70-thm-10`). -/
public theorem abs_convergent_num_sub_lt_of_le_den {x : ℝ} (hx : Irrational x)
    {n : ℕ} (hn : 1 < n) {p q : ℤ} (hq : 0 < q) (hqn : (q : ℝ) ≤ (GenContFract.of x).dens n)
    (hne : (p : ℝ) / q ≠ (GenContFract.of x).nums n / (GenContFract.of x).dens n) :
    |(GenContFract.of x).nums n - (GenContFract.of x).dens n * x| < |p - q * x| := by
  let g := of x
  let C := g.contsAux (n + 1)
  let P := g.contsAux n
  have hinf (k : ℕ) : ¬(of x).TerminatedAt k := by
    intro hk
    obtain ⟨r, hr⟩ := exists_rat_eq_of_terminates ⟨k, hk⟩
    exact hx ⟨r, hr.symm⟩
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hC : 0 < C.b := hq'.trans_le hqn
  have hP : 0 < P.b :=
    (Nat.cast_pos.mpr (Nat.fib_pos.mpr (by omega : 0 < n))).trans_le
      (fib_le_of_contsAux_b (Or.inr (hinf (n - 2))))
  obtain ⟨a, b, hp, hd⟩ := exists_continuant_coefficients hinf p q n
  change (p : ℝ) = a * C.a + b * P.a at hp
  change (q : ℝ) = a * C.b + b * P.b at hd
  have hb : b ≠ 0 := by
    rintro rfl
    apply hne
    apply (div_eq_div_iff hq'.ne' hC.ne').mpr
    simp only [Int.cast_zero, zero_mul, add_zero] at hp hd
    change (p : ℝ) * C.b = C.a * q
    rw [hp, hd]
    ring
  -- The fractional part at index n gives the complete quotient t > 1.
  obtain ⟨next, hnext⟩ := Option.ne_none_iff_exists'.mp
    (mt of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr (hinf n))
  obtain ⟨s, hs, hs₀, _⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hnext
  let t := s.fr⁻¹
  have ht : 1 < t := one_lt_inv_iff₀.mpr
    ⟨(IntFractPair.nth_stream_fr_nonneg hs).lt_of_ne' hs₀, IntFractPair.nth_stream_fr_lt_one hs⟩
  have hexact : x = (t * C.a + P.a) / (t * C.b + P.b) := by
    simpa [GenContFract.compExactValue, hs₀, nextConts, nextNum, nextDen, C, P, g, t]
      using compExactValue_correctness_of_stream_eq_some hs
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hrel : P.a - P.b * x = -t * (C.a - C.b * x) := by
    linear_combination - (eq_div_iff (by positivity)).mp hexact
  have herr : (p : ℝ) - q * x = (a - b * t) * (C.a - C.b * x) := by
    linear_combination hp - x * hd + b * hrel
  have hne_err : C.a - C.b * x ≠ 0 := by
    intro he
    obtain ⟨r, hr⟩ := exists_rat_eq_nth_conv x n
    apply hx ⟨r, hr.symm.trans ?_⟩
    exact (div_eq_iff hC.ne').mpr ((sub_eq_zero.mp he).trans (mul_comm _ _))
  have hcoeff := one_lt_abs_coeff_sub_mul hC hP (hd ▸ hq') (hd ▸ hqn) hb ht
  change |C.a - C.b * x| < |(p : ℝ) - q * x|
  rw [herr, abs_mul]
  simpa using mul_lt_mul_of_pos_right hcoeff (abs_pos.mpr hne_err)

end MetaMathlibExt
