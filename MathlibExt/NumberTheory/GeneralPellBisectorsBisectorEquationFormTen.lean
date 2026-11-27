/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralPellBisectors
import Mathlib.Tactic.LinearCombination

/-!
# Bisector-equation solutions from the powers of `1 + √2`

For every positive natural number `n`, the integers `a = f_{2n-1}`, `b = -f_{2n+1}` and
`c = f_{2n}` built from the negative Pell sequences for `d = 2` satisfy the bisector equation
`(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)`
(`MetaMathlibExt.bisector_equation_form_ten`).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (10)
(`integers-2024-A111-thm-3`).
-/

@[expose] public section

namespace MetaMathlibExt

/-- Recurrence for the `d = 2` negative Pell sequences. -/
private theorem succ_two (m : ℕ) :
    negPellF 2 (m + 1) = negPellF 2 m + 2 * negPellG 2 m ∧
      negPellG 2 (m + 1) = negPellF 2 m + negPellG 2 m := by
  obtain ⟨hF, hG⟩ := negPell_succ 2 m
  rw [negPellFund_two.2, negPellFund_two.1] at hF hG
  push_cast at hF hG
  refine ⟨?_, ?_⟩
  · linear_combination hF
  · linear_combination hG

/-- Norm identity for the `d = 2` negative Pell sequences. -/
private theorem norm_two (k : ℕ) :
    negPellF 2 k ^ 2 - 2 * negPellG 2 k ^ 2 = (-1 : ℤ) ^ k := by
  induction k with
  | zero =>
    obtain ⟨hF0, hG0⟩ := negPellF_zero_negPellG_zero 2
    rw [hF0, hG0]
    norm_num
  | succ m ih =>
    obtain ⟨hF, hG⟩ := succ_two m
    have hpow : (-1 : ℤ) ^ (m + 1) = -(-1 : ℤ) ^ m := by
      rw [pow_succ]
      ring
    rw [hF, hG, hpow]
    linear_combination -ih

/-- **Bisector-equation solutions from the powers of $1 + \sqrt{2}$.** The least solution of
$x^2 - 2 y^2 = -1$ in positive integers is $(1, 1)$; define integers $f_k$ and $g_k$ by
$f_k + g_k \sqrt{2} = (1 + \sqrt{2})^k$ for natural numbers $k$. For every natural number $n > 0$,
the integers $a = f_{2n-1}$, $b = -f_{2n+1}$ and $c = f_{2n}$ satisfy
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (10)
(`integers-2024-A111-thm-3`). -/
public theorem bisector_equation_form_ten (n : ℕ) (hn : 0 < n) :
    let a := negPellF 2 (2 * n - 1)
    let b := -negPellF 2 (2 * n + 1)
    let c := negPellF 2 (2 * n)
    (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := by
  dsimp only
  have h2n : 2 * n - 1 + 1 = 2 * n := by omega
  have hoA : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  have hoB : Odd (2 * n + 1) := ⟨n, by omega⟩
  have hA : negPellF 2 (2 * n - 1) ^ 2 - 2 * negPellG 2 (2 * n - 1) ^ 2 = -1 := by
    have h := norm_two (2 * n - 1)
    rw [hoA.neg_one_pow] at h
    exact h
  have hB : negPellF 2 (2 * n + 1) ^ 2 - 2 * negPellG 2 (2 * n + 1) ^ 2 = -1 := by
    have h := norm_two (2 * n + 1)
    rw [hoB.neg_one_pow] at h
    exact h
  have hC := (succ_two (2 * n - 1)).1
  rw [h2n] at hC
  have hD := succ_two (2 * n)
  have e1 : negPellF 2 (2 * n - 1) - negPellF 2 (2 * n) =
      -2 * negPellG 2 (2 * n - 1) := by
    linear_combination -hC
  have e2 : negPellF 2 (2 * n + 1) + negPellF 2 (2 * n) =
      2 * negPellG 2 (2 * n + 1) := by
    linear_combination hD.1 - 2 * hD.2
  have e3 : negPellF 2 (2 * n - 1) ^ 2 + 1 = 2 * negPellG 2 (2 * n - 1) ^ 2 := by
    linear_combination hA
  have e4 : negPellF 2 (2 * n + 1) ^ 2 + 1 = 2 * negPellG 2 (2 * n + 1) ^ 2 := by
    linear_combination hB
  have g1 : (negPellF 2 (2 * n - 1) - negPellF 2 (2 * n)) ^ 2 =
      4 * negPellG 2 (2 * n - 1) ^ 2 := by
    rw [e1]
    ring
  have g2 : (-negPellF 2 (2 * n + 1) - negPellF 2 (2 * n)) ^ 2 =
      4 * negPellG 2 (2 * n + 1) ^ 2 := by
    have h : -negPellF 2 (2 * n + 1) - negPellF 2 (2 * n) =
        -(negPellF 2 (2 * n + 1) + negPellF 2 (2 * n)) := by
      ring
    rw [h, e2]
    ring
  have g3 : (-negPellF 2 (2 * n + 1)) ^ 2 + 1 =
      2 * negPellG 2 (2 * n + 1) ^ 2 := by
    linear_combination e4
  rw [g1, g2, g3, e3]
  ring

end MetaMathlibExt
