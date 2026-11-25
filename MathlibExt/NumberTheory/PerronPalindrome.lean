/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.List.Monad
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith

/-!
# Perron's lemma on palindromic continued fractions

`MetaMathlibExt.exists_palindrome_continuedFraction_div` constructs the partial quotients
of a prime divided by a square root of minus one modulo that prime. Euclidean descent on
a symmetric matrix of determinant one produces equal quotients at the two ends of the list.
-/

namespace MetaMathlibExt

namespace exists_palindrome_continuedFraction_div

private def step (q : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![q, 1; 1, 0]

/-- The first column gives the numerator and denominator of the fold, starting from `(1, 0)`. -/
private theorem eval_product (qs : List ℕ) (hqs : ∀ a ∈ qs, 1 ≤ a) :
    let M := (qs.map step).prod
    0 < M 0 0 ∧ qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0 = (M 0 0 : ℚ) / M 1 0 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨hnum, hval⟩ := ih (fun a ha => hqs a (List.mem_cons_of_mem q ha))
    have hq := hqs q List.mem_cons_self
    simp only [List.bind_eq_flatMap, List.pure_def] at hval
    constructor
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, step] using
        Nat.add_pos_left (Nat.mul_pos hq hnum) ((qs.map step).prod 1 0)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, step, List.pure_def, hval, inv_div] using
        add_div' ((qs.map step).prod 1 0 : ℚ) q ((qs.map step).prod 0 0)
          (by exact_mod_cast hnum.ne')

/-- Factor a symmetric matrix of determinant one, removing one partial quotient at each end. -/
private theorem factor (a b c : ℕ) (hba : b < a) (hdet : a * c = b ^ 2 + 1) :
    ∃ qs : List ℕ, Even qs.length ∧ qs.reverse = qs ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      (qs.map step).prod = !![a, b; b, c] := by
  induction a using Nat.strong_induction_on generalizing b c with
  | ind a ih =>
    by_cases hb : b = 0
    · subst b
      obtain ⟨rfl, rfl⟩ := mul_eq_one.mp (by simpa using hdet : a * c = 1)
      exact ⟨[], by simp, rfl, by simp, Matrix.one_fin_two⟩
    have hc : 0 < c := by contrapose! hdet; simp [show c = 0 by omega]
    have hcb : c ≤ b := by
      by_contra! h
      have := Nat.mul_le_mul (show b + 1 ≤ a by omega) (show b + 1 ≤ c by omega)
      nlinarith [Nat.pos_of_ne_zero hb]
    -- Write b = c q + r. The middle matrix has first column (c, r).
    let q := b / c
    let r := b % c
    have hq : 1 ≤ q := Nat.div_pos hcb hc
    have hr : r < c := Nat.mod_lt _ hc
    have hbqr : c * q + r = b := Nat.div_add_mod _ _
    have hmod : r ^ 2 + 1 ≡ b ^ 2 + 1 [MOD c] := ((Nat.mod_modEq b c).pow 2).add_right 1
    have hdvd : c ∣ b ^ 2 + 1 := hdet ▸ dvd_mul_left _ _
    obtain ⟨d, hd⟩ := Nat.modEq_zero_iff_dvd.mp (hmod.trans hdvd.modEq_zero_nat)
    obtain ⟨qs, heven, hpal, hpos, hprod⟩ := ih c (by omega) r d hr hd.symm
    have ha : b * q + (d + q * r) = a := by
      apply Nat.eq_of_mul_eq_mul_right hc
      rw [hdet, ← hbqr]
      nlinarith only [hd]
    refine ⟨q :: (qs ++ [q]), ?_, ?_, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := heven
      exact ⟨n + 1, by simp [hn]; omega⟩
    · simp [hpal]
    · rw [List.forall_mem_cons, List.forall_mem_append]
      exact ⟨hq, hpos, by simpa using hq⟩
    · simp only [List.map_cons, List.map_append, List.map_nil, List.prod_cons, List.prod_append,
        List.prod_nil, mul_one, hprod]
      simpa [step, hbqr, Nat.mul_comm, Nat.add_comm] using ha

end exists_palindrome_continuedFraction_div

open exists_palindrome_continuedFraction_div in
set_option linter.unusedVariables false in
/-- **Perron's lemma.** Let $p$ be a prime with $p \equiv 1 \pmod 4$, and let $x_0$ be an integer
with $0 < x_0 < p/2$ and $x_0^2 \equiv -1 \pmod p$. Then there are positive integers
$q_0, q_1, \dots, q_m$ with $m + 1$ even and $q_i = q_{m-i}$ for every $i$ such that
$p / x_0 = [q_0; q_1, \dots, q_m] = q_0 + 1/(q_1 + 1/(\cdots + 1/q_m))$.

Since $x_0 < p/2$ forces $q_0 \ge 2$, such an expansion is the canonical continued fraction of
$p / x_0$ (the other expansion ends in $1$): the continued fraction of $p / x_0$ has an even
number of terms and is palindromic.

Source: Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76,
Lemma 1 (Perron) (`integers-2026-A76-lem-1`). -/
public theorem exists_palindrome_continuedFraction_div {p x₀ : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hx : (x₀ ^ 2 + 1) % p = 0) (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) :
    ∃ qs : List ℕ, Even qs.length ∧ qs.reverse = qs ∧ (∀ a ∈ qs, 1 ≤ a) ∧
      (p : ℚ) / x₀ = qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0 := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hx
  obtain ⟨qs, heven, hpal, hpos, hprod⟩ := factor p x₀ c (by omega) hc.symm
  refine ⟨qs, heven, hpal, hpos, ?_⟩
  simpa [hprod] using (eval_product qs hpos).2.symm

end MetaMathlibExt
