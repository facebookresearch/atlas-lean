/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HurwitzContinuedFractionFourSquares
import Mathlib.Tactic.NormNum

/-! # Tests for the errors, denominator growth and convergent bound of Hurwitz convergents -/

open MetaMathlibExt

namespace MetaMathlibExt.hurwitzQ_mul_sub_hurwitzP

-- The expansion of 2/5 is [0; 3, -2], with a rounding tie at the first iterate 5/2.
local notation "z" => (2 / 5 : ℂ)

private theorem iter_one : hurwitzIter z 1 = 5 / 2 := by
  norm_num [hurwitzIter, hurwitzRound, Complex.div_re, Complex.div_im, Complex.normSq_apply]

private theorem iter_two : hurwitzIter z 2 = -2 := by
  change (hurwitzIter z 1 - hurwitzRound (hurwitzIter z 1))⁻¹ = -2
  rw [iter_one]
  norm_num [hurwitzRound, Complex.div_re, Complex.div_im, Complex.normSq_apply]

private theorem legal_two : HurwitzLegal z 2 := by
  intro j hj
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl <;>
    norm_num [hurwitzDigit, iter_one, hurwitzIter, hurwitzRound, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]

-- Growth includes the last denominator, even when the preceding iterate was a rounding tie.
example : ‖hurwitzQ z 1‖ < ‖hurwitzQ z 2‖ :=
  norm_hurwitzQ_lt_succ z 1 (hn := legal_two)

-- At index one the product is nonzero and the two errors recover the last nonzero iterate.
example : hurwitzQ z 1 * z - hurwitzP z 1 = 1 / 5 ∧
    -(hurwitzQ z 0 * z - hurwitzP z 0) / (hurwitzQ z 1 * z - hurwitzP z 1) = -2 := by
  obtain ⟨hprod, hratio⟩ := hurwitzQ_mul_sub_hurwitzP z 1
    (fun j hj => legal_two j (Nat.lt_succ_of_lt hj))
  constructor
  · simpa [Finset.prod_range_succ, iter_one, iter_two] using hprod
  · simpa [iter_two] using (hratio le_rfl).symm

-- At the final legal index both the error and the quotient of consecutive errors vanish.
example : hurwitzQ z 2 * z - hurwitzP z 2 = 0 ∧
    -(hurwitzQ z 1 * z - hurwitzP z 1) / (hurwitzQ z 2 * z - hurwitzP z 2) = 0 := by
  have hstop : hurwitzIter z 3 = 0 := by
    change (hurwitzIter z 2 - hurwitzRound (hurwitzIter z 2))⁻¹ = 0
    rw [iter_two]
    norm_num [hurwitzRound]
  obtain ⟨hprod, hratio⟩ := hurwitzQ_mul_sub_hurwitzP z 2 legal_two
  constructor
  · simpa [Finset.prod_range_succ, hstop] using hprod
  · simpa [hstop] using (hratio (by decide)).symm

end MetaMathlibExt.hurwitzQ_mul_sub_hurwitzP

namespace MetaMathlibExt.norm_hurwitzQ_lt_succ

-- Both coordinates are rounding ties. The first legal next iterate is a diagonal digit.
local notation "corner" => ((-1 - Complex.I) / 2 : ℂ)

private theorem corner_iter : hurwitzIter corner 1 = -1 + Complex.I := by
  apply Complex.ext <;>
    norm_num [hurwitzIter, hurwitzRound, Complex.inv_re, Complex.inv_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

example : ‖hurwitzQ corner 0‖ < ‖hurwitzQ corner 1‖ := by
  apply norm_hurwitzQ_lt_succ
  intro j hj
  have hj₀ : j = 0 := Nat.lt_one_iff.mp hj
  subst j
  intro h
  have hz : hurwitzIter corner 1 = 0 := by
    change (hurwitzIter corner 0 - hurwitzDigit corner 0)⁻¹ = 0
    simp [h]
  rw [corner_iter] at hz
  have hre := congrArg Complex.re hz
  norm_num at hre

end MetaMathlibExt.norm_hurwitzQ_lt_succ

namespace MetaMathlibExt.norm_sub_hurwitz_convergent_le

-- The expansion of 2/5 is [0; 3, -2]; the bound is applied at the terminating index
-- (where the error vanishes) and at the two earlier legal indices.
private theorem legal_zero : HurwitzLegal (2 / 5 : ℂ) 0 :=
  fun j hj => (Nat.not_lt_zero j hj).elim

private theorem legal_one : HurwitzLegal (2 / 5 : ℂ) 1 :=
  fun j hj =>
    MetaMathlibExt.hurwitzQ_mul_sub_hurwitzP.legal_two j (Nat.lt_succ_of_lt hj)

example : ‖(2 / 5 : ℂ) - hurwitzP (2 / 5 : ℂ) 0 / hurwitzQ (2 / 5 : ℂ) 0‖ ≤
    1 / ‖hurwitzQ (2 / 5 : ℂ) 0‖ ^ 2 :=
  MetaMathlibExt.norm_sub_hurwitz_convergent_le _ _ legal_zero

example : ‖(2 / 5 : ℂ) - hurwitzP (2 / 5 : ℂ) 1 / hurwitzQ (2 / 5 : ℂ) 1‖ ≤
    1 / ‖hurwitzQ (2 / 5 : ℂ) 1‖ ^ 2 :=
  MetaMathlibExt.norm_sub_hurwitz_convergent_le _ _ legal_one

example : ‖(2 / 5 : ℂ) - hurwitzP (2 / 5 : ℂ) 2 / hurwitzQ (2 / 5 : ℂ) 2‖ ≤
    1 / ‖hurwitzQ (2 / 5 : ℂ) 2‖ ^ 2 :=
  MetaMathlibExt.norm_sub_hurwitz_convergent_le _ _
    MetaMathlibExt.hurwitzQ_mul_sub_hurwitzP.legal_two

end MetaMathlibExt.norm_sub_hurwitz_convergent_le
