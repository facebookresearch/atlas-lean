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
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Tactic.LinearCombination

/-!
# Rational approximation with bounded partial quotients

An upper bound on a finite prefix of the partial quotients of an irrational number gives a
strict lower bound on its distance from rationals in the corresponding denominator range.
-/

namespace MetaMathlibExt

open GenContFract
open GenContFract (of)

namespace BoundedPartialQuotients

private theorem dens_monotone (x : ℝ) : Monotone (of x).dens :=
  monotone_nat_of_le_succ fun _ ↦ of_den_mono

private theorem den_pos (x : ℝ) (n : ℕ) : 0 < (of x).dens n :=
  calc
    0 < (of x).dens 0 := by simp
    _ ≤ (of x).dens n := dens_monotone x (Nat.zero_le n)

/-- The cross product with an integer pair satisfies the integral continuant recurrence. -/
private theorem exists_int_cross {x : ℝ} (hinf : ∀ i, ¬(of x).TerminatedAt i) (p q : ℤ)
    (n : ℕ) : ∃ z : ℤ, (z : ℝ) = p * ((of x).contsAux n).b - q * ((of x).contsAux n).a := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨-q, by simp⟩
  | one => exact ⟨p - q * ⌊x⌋, by simp [of_h_eq_floor]⟩
  | more n ih₀ ih₁ =>
    obtain ⟨u, hu⟩ := ih₀
    obtain ⟨v, hv⟩ := ih₁
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp (hinf n)
    obtain ⟨h₁, b, hb⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hgp
    refine ⟨b * v + u, ?_⟩
    rw [Int.cast_add, Int.cast_mul, hu, hv, contsAux_recurrence hgp rfl rfl, hb, h₁]
    dsimp
    ring

/-- The determinant with the next convergent shows that even an unreduced representation
of a convergent has denominator at least the continuant denominator. -/
private theorem den_le_of_convs_eq {x : ℝ} (hinf : ∀ i, ¬(of x).TerminatedAt i) {n : ℕ}
    {p q : ℤ} (hq : 0 < (q : ℝ)) (heq : (of x).convs n = (p : ℝ) / q) :
    (of x).dens n ≤ q := by
  let g := of x
  have hcross := (div_eq_div_iff (den_pos x n).ne' hq.ne').mp heq
  obtain ⟨z, hz⟩ := exists_int_cross hinf p q (n + 2)
  change (z : ℝ) = p * g.dens (n + 1) - q * g.nums (n + 1) at hz
  have hdet := (SimpContFract.of x).determinant (hinf n)
  change g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) = _ at hdet
  have hscale : z * g.dens n = q * (-1 : ℝ) ^ (n + 1) := by
    linear_combination g.dens n * hz + q * hdet - g.dens (n + 1) * hcross
  have habs : |(z : ℝ)| * g.dens n = q := by
    simpa [abs_mul, abs_pow, abs_of_pos hq, abs_of_pos (den_pos x n), g]
      using congrArg abs hscale
  have hz₀ : z ≠ 0 := by
    rintro rfl
    exact hq.ne (by simpa using habs)
  have hz₁ : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz₀
  rw [← habs]
  simpa using mul_le_mul_of_nonneg_right hz₁ (den_pos x n).le

/-- The next complete quotient is strictly below its integer part plus one. The preceding
denominator contributes at most one more copy of the current denominator. -/
private theorem convergent_lower_bound {x A : ℝ} {n : ℕ} (hinf : ¬(of x).TerminatedAt n)
    (ha : ∀ b : ℝ, (of x).partDens.get? n = some b → b ≤ A) :
    1 / ((A + 2) * (of x).dens n ^ 2) < |x - (of x).convs n| := by
  obtain ⟨next, hnext⟩ := Option.ne_none_iff_exists'.mp
    (mt of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr hinf)
  obtain ⟨s, hs, hs₀, rfl⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hnext
  have hdigit := partDen_eq_s_b (get?_of_eq_some_of_succ_get?_intFractPair_stream hnext)
  have ht : s.fr⁻¹ < A + 1 :=
    (Int.lt_floor_add_one _).trans_le (add_le_add_left (ha _ hdigit) 1)
  let D := (of x).dens n
  let P := ((of x).contsAux n).b
  have hD : 0 < D := den_pos x n
  have hP : 0 ≤ P := zero_le_of_contsAux_b
  have hPD : P ≤ D := by
    cases n with
    | zero => simp [P, D]
    | succ k => exact of_den_mono
  have hfr : 0 < s.fr := (IntFractPair.nth_stream_fr_nonneg hs).lt_of_ne' hs₀
  have herr : x - (of x).convs n = (-1) ^ n / (D * (s.fr⁻¹ * D + P)) := by
    simpa only [hs₀, ite_false, D, P, den_eq_conts_b, nth_cont_eq_succ_nth_contAux] using
      sub_convs_eq hs
  rw [herr, abs_div, abs_neg_one_pow, abs_of_pos (by positivity)]
  apply one_div_lt_one_div_of_lt (by positivity)
  calc
    D * (s.fr⁻¹ * D + P) < D * ((A + 1) * D + D) :=
      mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right ht hD) hPD) hD
    _ = (A + 2) * D ^ 2 := by ring

end BoundedPartialQuotients

open BoundedPartialQuotients

set_option linter.unusedVariables false in
/-- **Lower bound for $|x - p/q|$ from bounded partial quotients.** Let $x$ be an irrational real
number with continued fraction expansion $[a_0; a_1, a_2, \dots]$, where $a_0 = \lfloor x \rfloor$,
and with convergents $p_k / q_k$. Let $M \ge 1$ and $N \ge 0$ be integers with
$q_N \le M < q_{N+1}$, and let $a$ be a real number with $a \ge a_j$ for every $0 \le j \le N + 1$.
Then

$$\left|x - \frac{p}{q}\right| > \frac{1}{(a + 2) q^2}$$

for all integers $p$ and $q$ with $0 < q < M$.

The source takes $a$ to be the maximum of $a_0, \dots, a_{N+1}$; since the bound weakens as $a$
grows, the two forms are equivalent.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Lemma 3
(`integers-2025-A70-lem-3`). -/
public theorem one_div_partialQuotient_bound_lt_abs_sub {x : ℝ} (hx : Irrational x)
    {M N : ℕ} (hM : 0 < M) (hNM : (GenContFract.of x).dens N ≤ M)
    (hMN : (M : ℝ) < (GenContFract.of x).dens (N + 1)) {aM : ℝ} (ha0 : (⌊x⌋ : ℝ) ≤ aM)
    (ha : ∀ j ≤ N, ∀ b : ℝ, (GenContFract.of x).partDens.get? j = some b → b ≤ aM)
    {p q : ℤ} (hq : 0 < q) (hqM : q < M) :
    1 / ((aM + 2) * (q : ℝ) ^ 2) < |x - p / q| := by
  have hinf (i : ℕ) : ¬(of x).TerminatedAt i := by
    intro hi
    obtain ⟨r, hr⟩ := exists_rat_eq_of_terminates ⟨i, hi⟩
    exact hx ⟨r, hr.symm⟩
  obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp (hinf 0)
  have hdigit := partDen_eq_s_b hgp
  have hA : 1 ≤ aM := (of_one_le_get?_partDen hdigit).trans (ha 0 (Nat.zero_le _) _ hdigit)
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  let r := Rat.divInt p q
  have hr : (r : ℝ) = (p : ℝ) / q := by simp [r, Rat.divInt_eq_div]
  have hrq : (r.den : ℝ) ≤ q := by
    exact_mod_cast Int.le_of_dvd hq (Rat.den_dvd p q)
  -- Any violation is close enough for Legendre's theorem, even after reducing p/q.
  by_contra! h
  have hsmall : |x - r| < 1 / (2 * (r.den : ℝ) ^ 2) := by
    rw [hr]
    refine h.trans_lt (one_div_lt_one_div_of_lt (by positivity) ?_)
    calc
      2 * (r.den : ℝ) ^ 2 ≤ 2 * (q : ℝ) ^ 2 := by gcongr
      _ < (aM + 2) * (q : ℝ) ^ 2 := mul_lt_mul_of_pos_right (by linarith) (by positivity)
  obtain ⟨n, heq⟩ := Real.exists_convs_eq_rat hsmall
  rw [hr] at heq
  have hD := den_le_of_convs_eq hinf hq' heq
  have hn : n ≤ N := by
    by_contra! hlt
    exact (not_le_of_gt (lt_trans (by exact_mod_cast hqM) hMN))
      ((dens_monotone x hlt).trans hD)
  have hbound := convergent_lower_bound (hinf n) (ha n hn)
  rw [heq] at hbound
  apply hbound.not_ge (h.trans ?_)
  apply one_div_le_one_div_of_le (by positivity [den_pos x n])
  gcongr
  exact (den_pos x n).le

end MetaMathlibExt
