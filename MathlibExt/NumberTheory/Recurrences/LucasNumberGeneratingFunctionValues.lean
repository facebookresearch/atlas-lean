/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer values of the Lucas number generating function

Inside its interval of convergence, the Lucas generating function takes integer values
exactly at certain consecutive Fibonacci and Lucas ratios and at `-1/2`.
-/

namespace MetaMathlibExt

namespace lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius

-- For a reduced input p/r, this form is the denominator after clearing fractions.
private def form (p r : ℤ) : ℤ := r ^ 2 - p * r - p ^ 2

private def advance (v : ℤ × ℤ) : ℤ × ℤ := (v.1 + v.2, v.1 + 2 * v.2)

private lemma form_advance (p r : ℤ) :
    form (p + r) (p + 2 * r) = form p r := by unfold form; ring

private def pairAt (s : ℕ → ℕ) (n : ℕ) : ℤ × ℤ := (s n, s (n + 1))

private lemma advance_pairAt {s : ℕ → ℕ} (hs : ∀ n, s (n + 2) = s n + s (n + 1)) (n : ℕ) :
    advance (pairAt s n) = pairAt s (n + 2) := by
  apply Prod.ext
  · simp [advance, pairAt, hs n]
  · change (s n : ℤ) + 2 * s (n + 1) = s ((n + 1) + 2)
    rw [hs (n + 1), show n + 1 + 1 = n + 2 by rfl, hs n]
    push_cast
    ring

private lemma advance_fib (i : ℕ) :
    advance (pairAt Nat.fib (2 * i)) = pairAt Nat.fib (2 * (i + 1)) :=
  advance_pairAt (fun _ ↦ Nat.fib_add_two) _

private lemma advance_lucas (i : ℕ) :
    advance (pairAt lucasNumber (2 * i + 1)) = pairAt lucasNumber (2 * (i + 1) + 1) :=
  advance_pairAt (fun n ↦ add_comm (lucasNumber (n + 1)) _) _

-- Two steps of the Fibonacci recurrence preserve the form. The exceptional input
-- (-1, 2) advances to (1, 3), the first of the indicated Lucas pairs.
private inductive ValuePair : ℤ × ℤ → Prop
  | zero : ValuePair (0, 1)
  | negHalf : ValuePair (-1, 2)
  | step {v} : ValuePair v → ValuePair (advance v)

private lemma valuePair_iff (v : ℤ × ℤ) :
    ValuePair v ↔ (∃ i, v = pairAt Nat.fib (2 * i) ∨ v = pairAt lucasNumber (2 * i + 1)) ∨
      v = (-1, 2) := by
  constructor
  · intro h
    induction h with
    | zero => exact Or.inl ⟨0, Or.inl rfl⟩
    | negHalf => exact Or.inr rfl
    | step h ih =>
      rcases ih with ⟨i, rfl | rfl⟩ | rfl
      · exact Or.inl ⟨i + 1, Or.inl (advance_fib i)⟩
      · exact Or.inl ⟨i + 1, Or.inr (advance_lucas i)⟩
      · exact Or.inl ⟨0, Or.inr (by decide)⟩
  · rintro (⟨i, rfl | rfl⟩ | rfl)
    · induction i with
      | zero => exact .zero
      | succ i ih => exact advance_fib i ▸ ih.step
    · induction i with
      | zero => exact ValuePair.negHalf.step
      | succ i ih => exact advance_lucas i ▸ ih.step
    · exact .negHalf

-- In lowest terms, integrality forces the form to divide 5.
private lemma form_dvd_five {p r n : ℤ} (hc : IsCoprime p r)
    (hn : r * (2 * r - p) = form p r * n) : form p r ∣ 5 := by
  have hcop : IsCoprime (form p r) r := by
    rw [show form p r = r * (r - p) - p ^ 2 by unfold form; ring,
      IsCoprime.mul_sub_left_left_iff]
    exact hc.pow_left
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left (show form p r ∣ r * (2 * r - p) from ⟨n, hn⟩)
  apply (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right
  refine ⟨k * (p + 3 * r) - 1, ?_⟩
  unfold form at hk ⊢
  linear_combination (p + 3 * r) * hk

private lemma descent (p r : ℤ) (hr : 0 < r) (hl : -r < p) (hu : p < r)
    (hpos : 0 < form p r) (hd : form p r ∣ 5) : ValuePair (p, r) := by
  by_cases hp : 0 < p
  · have hpred : form (2 * p - r) (r - p) = form p r := by unfold form; ring
    have hu' : 2 * p - r < r - p := by
      by_contra! h
      unfold form at hpos
      nlinarith [mul_nonneg (show 0 ≤ 3 * p - 2 * r by omega) (show 0 ≤ r + p by omega),
        sq_nonneg (r - p)]
    have ih := descent (2 * p - r) (r - p) (by omega) (by omega) hu'
      (hpred ▸ hpos) (hpred ▸ hd)
    convert ih.step using 1
    simp [advance]
    omega
  · have hle := Int.le_of_dvd (by decide : (0 : ℤ) < 5) hd
    have hr2 : r ≤ 2 := by
      unfold form at hle
      nlinarith [mul_nonneg (show 0 ≤ -p by omega) (show 0 ≤ r + p by omega),
        sq_nonneg (r - 3)]
    interval_cases r <;> interval_cases p <;> first
      | exact ValuePair.negHalf
      | exact ValuePair.zero
      | norm_num [form] at hd
termination_by r.toNat
decreasing_by omega

private lemma pair_invariants {v : ℤ × ℤ} (h : ValuePair v) :
    0 < v.2 ∧ -v.2 < v.1 ∧ 0 < form v.1 v.2 ∧ form v.1 v.2 ∣ 5 ∧
      form v.1 v.2 ∣ 2 * v.2 - v.1 := by
  induction h with
  | zero => decide
  | negHalf => decide
  | @step v _ ih =>
    rcases ih with ⟨hr, hp, hpos, hd, hk⟩
    simp only [advance, form_advance]
    refine ⟨by omega, by omega, hpos, hd, ?_⟩
    convert dvd_sub (dvd_mul_of_dvd_left hd v.2) hk using 1
    ring

private lemma radius_bounds {x : ℝ} (hx : |x| < 2 / (1 + Real.sqrt 5)) :
    -1 < x ∧ x < 1 ∧ 0 < 1 - x - x ^ 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs₀ := Real.sqrt_nonneg 5
  have hs₃ : Real.sqrt 5 < 3 := by nlinarith
  have hr : 2 / (1 + Real.sqrt 5) = (Real.sqrt 5 - 1) / 2 := by
    apply (div_eq_iff (by positivity)).2
    nlinarith
  rw [hr, abs_lt] at hx
  obtain ⟨hl, hu⟩ := hx
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [mul_pos (show 0 < Real.sqrt 5 - (2 * x + 1) by linarith)
    (show 0 < Real.sqrt 5 + (2 * x + 1) by linarith)]

private lemma eval_eq_int_iff {p r n : ℤ} (hr : 0 < r) (hpos : 0 < form p r) :
    (2 - (p : ℚ) / r) / (1 - (p : ℚ) / r - ((p : ℚ) / r) ^ 2) = n ↔
      r * (2 * r - p) = form p r * n := by
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hden : (1 - (p : ℚ) / r - ((p : ℚ) / r) ^ 2) * r ^ 2 = (form p r : ℚ) := by
    unfold form
    push_cast
    field_simp
  have hne : (form p r : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hne' : 1 - (p : ℚ) / r - ((p : ℚ) / r) ^ 2 ≠ 0 := by
    apply left_ne_zero_of_mul (b := (r : ℚ) ^ 2)
    rwa [hden]
  rw [div_eq_iff hne', ← mul_left_inj' (pow_ne_zero 2 hr'), mul_assoc, hden]
  have hnum : (2 - (p : ℚ) / r) * r ^ 2 = r * (2 * r - p) := by field_simp
  rw [hnum, mul_comm (n : ℚ)]
  exact_mod_cast Iff.rfl

private lemma int_value_of_pair {v : ℤ × ℤ} (h : ValuePair v) :
    let q := (v.1 : ℚ) / v.2
    ∃ n : ℤ, (2 - q) / (1 - q - q ^ 2) = n := by
  obtain ⟨hr, _, hpos, _, k, hk⟩ := pair_invariants h
  refine ⟨v.2 * k, (eval_eq_int_iff hr hpos).2 ?_⟩
  rw [hk]
  ring

end lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius

open lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius

/-- **Integer values of the Lucas number generating function in its interval of convergence.**
Let $F_n$ be the Fibonacci numbers and $L_n$ the Lucas numbers, given by $L_0 = 2$, $L_1 = 1$
and $L_{n+2} = L_{n+1} + L_n$. For a rational number $q$ with $|q| < 2 / (1 + \sqrt 5)$, the
number $(2 - q) / (1 - q - q^2)$ is an integer if and only if $q = -1/2$, or
$q = F_{2i} / F_{2i+1}$ or $q = L_{2i+1} / L_{2i+2}$ for some $i \in \mathbb{N}$.

This is the case $a = b = 1$ of the generating function $(2 - at) / (1 - at - bt^2)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.8
(`fq-2024-tsuno05142024-cor-1.8`). -/
public theorem lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (1 + Real.sqrt 5)) :
    (∃ n : ℤ, (2 - q) / (1 - q - q ^ 2) = n) ↔
      (∃ i : ℕ, q = (Nat.fib (2 * i) : ℚ) / Nat.fib (2 * i + 1) ∨
        q = (lucasNumber (2 * i + 1) : ℚ) / lucasNumber (2 * i + 2)) ∨ q = -1 / 2 := by
  constructor
  · rintro ⟨n, hn⟩
    let p := q.num
    let r : ℤ := q.den
    have hr : 0 < r := by dsimp [r]; exact_mod_cast q.den_pos
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hq' : (p : ℚ) / r = q := by simpa [p, r] using q.num_div_den
    have hx : |(p : ℝ) / r| < 2 / (1 + Real.sqrt 5) := by
      rw [← hq'] at hq
      push_cast at hq
      exact hq
    obtain ⟨hl, hu, hpos⟩ := radius_bounds hx
    have hl' : -r < p := by
      exact_mod_cast (show -(r : ℝ) < p by simpa using (lt_div_iff₀ hr').1 hl)
    have hu' : p < r := by simpa using (div_lt_iff₀ hr').1 hu
    have hform : 0 < form p r := by
      unfold form
      field_simp at hpos
      exact_mod_cast (show 0 < (r : ℝ) ^ 2 - p * r - p ^ 2 by linarith only [hpos])
    have hd := form_dvd_five q.isCoprime_num_den ((eval_eq_int_iff hr hform).1 (hq' ▸ hn))
    obtain (⟨i, hf | hL⟩ | hneg) := (valuePair_iff _).1 (descent p r hr hl' hu' hform hd)
    · refine Or.inl ⟨i, Or.inl ?_⟩
      simpa [← hq', pairAt] using congrArg (fun v : ℤ × ℤ ↦ (v.1 : ℚ) / v.2) hf
    · refine Or.inl ⟨i, Or.inr ?_⟩
      simpa [← hq', pairAt] using congrArg (fun v : ℤ × ℤ ↦ (v.1 : ℚ) / v.2) hL
    · exact Or.inr (by simpa [← hq'] using congrArg (fun v : ℤ × ℤ ↦ (v.1 : ℚ) / v.2) hneg)
  · rintro (⟨i, rfl | rfl⟩ | rfl)
    · simpa [pairAt] using int_value_of_pair ((valuePair_iff _).2 (Or.inl ⟨i, Or.inl rfl⟩))
    · simpa [pairAt] using int_value_of_pair ((valuePair_iff _).2 (Or.inl ⟨i, Or.inr rfl⟩))
    · exact ⟨2, by norm_num⟩

end MetaMathlibExt
