/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralPellBisectorsBisectorEquationFormNine
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.GeneralPellBisectorsBisectorEquationFormNine

open MetaMathlibExt

private theorem step {d n x y : ℕ} {a b : ℤ}
    (hx : negPellFundX d = x) (hy : negPellFundY d = y)
    (h : negPellF d n = a ∧ negPellG d n = b) :
    negPellF d (n + 1) = a * x + d * b * y ∧ negPellG d (n + 1) = a * y + b * x := by
  simpa only [hx, hy, h.1, h.2] using negPell_succ d n

private theorem powersTwo : (negPellF 2 3 = 7 ∧ negPellG 2 3 = 5) ∧
    (negPellF 2 6 = 99 ∧ negPellG 2 6 = 70) ∧ negPellF 2 9 = 1393 := by
  have next {n : ℕ} {a b : ℤ} (h : negPellF 2 n = a ∧ negPellG 2 n = b) :=
    step negPellFund_two.2 negPellFund_two.1 h
  have h2 : negPellF 2 2 = 3 ∧ negPellG 2 2 = 2 := next negPellF_two_one
  have h3 : negPellF 2 3 = 7 ∧ negPellG 2 3 = 5 := next h2
  have h4 : negPellF 2 4 = 17 ∧ negPellG 2 4 = 12 := next h3
  have h5 : negPellF 2 5 = 41 ∧ negPellG 2 5 = 29 := next h4
  have h6 : negPellF 2 6 = 99 ∧ negPellG 2 6 = 70 := next h5
  have h7 : negPellF 2 7 = 239 ∧ negPellG 2 7 = 169 := next h6
  have h8 : negPellF 2 8 = 577 ∧ negPellG 2 8 = 408 := next h7
  exact ⟨h3, h6, (next h8).1⟩

-- Compute both addition coordinates directly by the one-step recurrence, not `negPell_add`.
example :
    negPellF 2 (3 + 3) = negPellF 2 3 * negPellF 2 3 + 2 * negPellG 2 3 * negPellG 2 3 ∧
    negPellG 2 (3 + 3) = negPellF 2 3 * negPellG 2 3 + negPellG 2 3 * negPellF 2 3 := by
  change negPellF 2 6 = _ ∧ negPellG 2 6 = _
  norm_num [powersTwo.1.1, powersTwo.1.2, powersTwo.2.1.1, powersTwo.2.1.2]

-- Check the norm at an odd and an even power independently of `negPell_norm_of_solvable`.
example : (negPellF 2 3 ^ 2 - 2 * negPellG 2 3 ^ 2 = -1) ∧
    (negPellF 2 6 ^ 2 - 2 * negPellG 2 6 ^ 2 = 1) := by
  norm_num [powersTwo.1.1, powersTwo.1.2, powersTwo.2.1.1, powersTwo.2.1.2]

-- Example 4(b), with `m = 2` and `n = 1`: the divisor is `5`, not a unit.
example :
    let a := negPellF 2 3
    let b := negPellF 2 9
    let c := negPellG 2 6 / negPellG 2 3
    negPellG 2 3 ∣ negPellG 2 6 ∧ c = 14 ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := by
  dsimp only
  rw [powersTwo.1.1, powersTwo.1.2, powersTwo.2.1.2, powersTwo.2.2]
  decide

private theorem fundFifty : negPellFundX 50 = 7 ∧ negPellFundY 50 = 1 := by
  have stepOne : (7 : ℕ) ^ 2 + 1 = 50 * 1 ^ 2 := by decide
  have h := negPellFund_spec ⟨1, by decide, 7, stepOne⟩
  have hy := negPellFundY_le (by decide : 0 < 1) ⟨7, stepOne⟩
  have hY : negPellFundY 50 = 1 := le_antisymm hy h.1
  have hX : negPellFundX 50 = 7 := by
    apply (Nat.pow_left_inj (by decide : (2 : ℕ) ≠ 0)).mp
    rw [hY] at h
    omega
  exact ⟨hX, hY⟩

-- The square factor of `50` does not obstruct Form (9). Here `m = 1` and `n = 2`.
example :
    let a := negPellF 50 3
    let b := negPellF 50 5
    let c := negPellG 50 4 / negPellG 50 1
    negPellG 50 1 ∣ negPellG 50 4 ∧ c = 2772 ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) := by
  have next {n : ℕ} {a b : ℤ} (h : negPellF 50 n = a ∧ negPellG 50 n = b) :=
    step fundFifty.1 fundFifty.2 h
  have h1 : negPellF 50 1 = 7 ∧ negPellG 50 1 = 1 := next (negPellF_zero_negPellG_zero 50)
  have h2 : negPellF 50 2 = 99 ∧ negPellG 50 2 = 14 := next h1
  have h3 : negPellF 50 3 = 1393 ∧ negPellG 50 3 = 197 := next h2
  have h4 : negPellF 50 4 = 19601 ∧ negPellG 50 4 = 2772 := next h3
  have h5 : negPellF 50 5 = 275807 := (next h4).1
  dsimp only
  rw [h1.2, h3.1, h4.2, h5]
  decide

-- A client can apply the public theorem at nonsquarefree `d` with a Pell witness.
example :
    let a := negPellF 50 3
    let b := negPellF 50 5
    let c := negPellG 50 4 / negPellG 50 1
    negPellG 50 1 ∣ negPellG 50 4 ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) :=
  bisector_equation_form_nine 50 1 2 (by decide) ⟨7, 1, by decide⟩ (by decide) (by decide)

end MathlibExtTest.NumberTheory.GeneralPellBisectorsBisectorEquationFormNine
