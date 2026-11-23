/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Lifts of singular points of bivariate polynomials

A first-order Taylor expansion modulo `p²` shows that all lifts of a singular point have the
same polynomial value modulo `p²`. See the [authors' preprint](https://arxiv.org/abs/2411.05366).
-/

namespace MetaMathlibExt

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
