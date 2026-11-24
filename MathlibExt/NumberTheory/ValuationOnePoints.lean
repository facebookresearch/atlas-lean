/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Polynomial lifts modulo a prime square

A simple root modulo `p` has at most one lift to a root modulo `p²`. For a bivariate
polynomial, all lifts of a singular point have the same value modulo `p²`.
See the [authors' preprint](https://arxiv.org/abs/2411.05366).
-/

namespace MetaMathlibExt

/-- **At most one lift has valuation above one.** Let $p$ be a prime, $g \in \mathbb{Z}[x]$ and
$r$ an integer with $0 \le r < p$ such that $g(r)$ and $g'(r)$ are not both divisible by $p$.
Then at most one $k \in \{0, \dots, p - 1\}$ satisfies $p^2 \mid g(r + kp)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 1
(`integers-2026-A82-prop-1`). -/
public theorem card_lift_padicVal_gt_one_le_one {p : ℕ} (hp : p.Prime) (g : Polynomial ℤ)
    {r : ℕ} (hr : r < p)
    (hroot : ¬ ((p : ℤ) ∣ g.eval (r : ℤ) ∧ (p : ℤ) ∣ (Polynomial.derivative g).eval (r : ℤ))) :
    ((Finset.range p).filter fun k : ℕ => (p : ℤ) ^ 2 ∣ g.eval ((r : ℤ) + k * p)).card ≤ 1 := by
  have linear (k : ℕ) (hk : (p : ℤ) ^ 2 ∣ g.eval ((r : ℤ) + k * p)) :
      (p : ℤ) ^ 2 ∣ g.derivative.eval (r : ℤ) * k * p + g.eval (r : ℤ) := by
    obtain ⟨c, hc⟩ := g.exists_mul_sq_add_linear_part_eq_eval_add (r : ℤ) ((k : ℤ) * p)
    rw [← hc, add_assoc, mul_pow, ← mul_assoc c, Int.dvd_add_right (dvd_mul_left _ _)] at hk
    simpa only [mul_assoc] using hk
  apply Finset.card_le_one.mpr
  intro k hk l hl
  simp only [Finset.mem_filter, Finset.mem_range] at hk hl
  have h₁ := linear k hk.2
  have h₂ := linear l hl.2
  have hval : (p : ℤ) ∣ g.eval (r : ℤ) :=
    (Int.dvd_add_right (dvd_mul_left _ _)).mp ((dvd_pow_self _ (by decide : 2 ≠ 0)).trans h₁)
  have hdiff := dvd_sub h₂ h₁
  rw [add_sub_add_right_eq_sub, ← sub_mul, ← mul_sub, sq] at hdiff
  have hp₀ : (p : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.zero_lt_of_lt hr)
  have hprod := (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd (Int.dvd_of_mul_dvd_mul_right hp₀ hdiff)
  have hkl := Nat.modEq_iff_dvd.mpr (hprod.resolve_left fun hd => hroot ⟨hval, hd⟩)
  exact hkl.eq_of_lt_of_lt hk.1 hl.1

open MvPolynomial

/-- The linear terms of a lift account for its change in value up to a multiple of `p²`. -/
private lemma exists_eval_lift_remainder (f : MvPolynomial (Fin 2) ℤ) (r s k l p : ℤ) :
    ∃ q : ℤ, eval ![r + k * p, s + l * p] f = eval ![r, s] f +
      p * (k * eval ![r, s] (pderiv 0 f) + l * eval ![r, s] (pderiv 1 f)) + p ^ 2 * q := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by simp only [map_add, ha, hb]; ring⟩
  | mul_X f i ih =>
    obtain ⟨q, hq⟩ := ih
    let d := k * eval ![r, s] (pderiv 0 f) + l * eval ![r, s] (pderiv 1 f)
    refine ⟨q * ![r + k * p, s + l * p] i + d * ![k, l] i, ?_⟩
    fin_cases i <;> simp [d, hq] <;> ring

set_option linter.unusedVariables false in
/-- **Lifts of a singular point with valuation one.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $r, s$ be integers in
$\{0, \dots, p - 1\}$ such that $p$ divides $f(r, s)$, $f_x(r, s)$ and $f_y(r, s)$. Then the
number of pairs $(k, l)$ with $0 \le k, l < p$, $p \mid f(r + kp, s + lp)$ and
$p^2 \nmid f(r + kp, s + lp)$ is $0$ if $p^2 \mid f(r, s)$, and $p^2$ otherwise.

The cited statement prints the two cases swapped. By the paper's eq. (7) every lift
$f(r + kp, s + lp)$ is congruent to $f(r, s)$ modulo $p^2$. The printed version fails for
$f = x^2 + y^2 + 3$, $p = 3$, $(r, s) = (0, 0)$: $f(0, 0) = 3$ is not divisible by $9$, and all
$9$ lifts have valuation $1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 3 (`integers-2026-A82-cor-3`). -/
public theorem card_lift_padicVal_eq_one_of_singular {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hx : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f))
    (hy : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      if (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ), s] f then 0 else p ^ 2 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have lift (k l : ℕ) : eval ![(r : ℤ), s] f ≡
      eval ![(r : ℤ) + k * p, (s : ℤ) + l * p] f [ZMOD (p : ℤ) ^ 2] := by
    obtain ⟨q, hq⟩ := exists_eval_lift_remainder f r s k l p
    rw [Int.modEq_iff_dvd, hq, ha, hb]
    exact ⟨k * a + l * b + q, by ring⟩
  by_cases h : (p : ℤ) ^ 2 ∣ eval ![(r : ℤ), s] f
  · rw [ite_eq_left h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun ⟨k, l⟩ _ hkl => hkl.2 ((lift k l).dvd_iff.mp h)
  · rw [ite_eq_right h, Finset.filter_true_of_mem]
    · simp [sq]
    · intro ⟨k, l⟩ _
      have hl := lift k l
      exact ⟨(hl.of_dvd (dvd_pow_self _ (by decide))).dvd_iff.mp hcurve,
        fun hkl => h (hl.dvd_iff.mpr hkl)⟩

end MetaMathlibExt
