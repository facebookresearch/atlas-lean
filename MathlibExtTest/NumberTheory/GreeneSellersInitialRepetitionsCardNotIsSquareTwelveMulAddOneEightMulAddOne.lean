/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GreeneSellersInitialRepetitionsCardNotIsSquareTwelveMulAddOneEightMulAddOne
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete simultaneous-nonresidue counts

We apply the specialised counting theorem at the primes $2$, $3$, $5$, $7$, and $11$.
For the general formula, we check exact residue sets and the three possible signs of the
correction independently, including at the smallest odd prime and with a negative coefficient.
-/

namespace MathlibExtTest.NumberTheory

namespace GreeneSellersInitialRepetitionsCardNotIsSquareTwelveMulAddOneEightMulAddOne

@[expose] public section

open scoped Classical in
example :
    ((Finset.Icc 1 (2 - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod 2) ∧
        ¬IsSquare ((8 * r + 1 : ℕ) : ZMod 2)).card = 0 := by
  simpa using MetaMathlibExt.card_not_isSquare_twelve_mul_add_one_eight_mul_add_one
    2 (by norm_num)

open scoped Classical in
example :
    ((Finset.Icc 1 (3 - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod 3) ∧
        ¬IsSquare ((8 * r + 1 : ℕ) : ZMod 3)).card = 0 := by
  simpa using MetaMathlibExt.card_not_isSquare_twelve_mul_add_one_eight_mul_add_one
    3 (by norm_num)

open scoped Classical in
example :
    ((Finset.Icc 1 (5 - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod 5) ∧
        ¬IsSquare ((8 * r + 1 : ℕ) : ZMod 5)).card = 0 := by
  simpa using MetaMathlibExt.card_not_isSquare_twelve_mul_add_one_eight_mul_add_one
    5 (by norm_num)

open scoped Classical in
example :
    ((Finset.Icc 1 (7 - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod 7) ∧
        ¬IsSquare ((8 * r + 1 : ℕ) : ZMod 7)).card = 1 := by
  simpa using MetaMathlibExt.card_not_isSquare_twelve_mul_add_one_eight_mul_add_one
    7 (by norm_num)

open scoped Classical in
example :
    ((Finset.Icc 1 (11 - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod 11) ∧
        ¬IsSquare ((8 * r + 1 : ℕ) : ZMod 11)).card = 3 := by
  simpa using MetaMathlibExt.card_not_isSquare_twelve_mul_add_one_eight_mul_add_one
    11 (by norm_num)

end

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

-- At the smallest odd prime the set is empty and the correction vanishes.
example :
    ((Finset.range 3).filter fun r : ℕ =>
      legendreSym 3 ((r : ℤ) + 1) = -1 ∧ legendreSym 3 (-r + 1 : ℤ) = -1) = ∅ ∧
    4 * ((3 / 4 : ℕ) : ℤ) -
      (legendreSym 3 1 - legendreSym 3 (-2)) * (legendreSym 3 (-1) - legendreSym 3 2) = 0 := by
  constructor
  · decide
  · norm_num

-- Modulo five the product of differences is positive and cancels the floor term.
example :
    ((Finset.range 5).filter fun r : ℕ =>
      legendreSym 5 (2 * r + 1) = -1 ∧ legendreSym 5 (3 * r + 1) = -1) = ∅ ∧
    4 * ((5 / 4 : ℕ) : ℤ) -
      (legendreSym 5 2 - legendreSym 5 1) * (legendreSym 5 3 - legendreSym 5 (-1)) = 0 := by
  constructor
  · decide
  · norm_num

-- With a negative slope modulo eleven, the negative correction product adds one to the count.
example :
    ((Finset.range 11).filter fun r : ℕ =>
      legendreSym 11 ((r : ℤ) + 1) = -1 ∧ legendreSym 11 (-3 * r + 1) = -1) = {5, 7, 9} ∧
    4 * ((11 / 4 : ℕ) : ℤ) -
      (legendreSym 11 1 - legendreSym 11 (-4)) * (legendreSym 11 (-3) - legendreSym 11 4) = 12 := by
  constructor
  · decide
  · norm_num

-- The public formula gives the count for the same signed slopes.
example : ((Finset.range 11).filter fun r : ℕ =>
    legendreSym 11 ((r : ℤ) + 1) = -1 ∧ legendreSym 11 (-3 * r + 1) = -1).card = 3 := by
  have h := MetaMathlibExt.four_mul_card_legendreSym_pair_eq_neg_one
    11 (by decide) 1 (-3) (by decide)
  have hvalue : 4 * ((11 / 4 : ℕ) : ℤ) -
      (legendreSym 11 1 - legendreSym 11 (-3 - 1)) *
        (legendreSym 11 (-3) - legendreSym 11 (1 - (-3))) = 12 := by norm_num
  rw [hvalue] at h
  simp only [one_mul] at h
  omega

end GreeneSellersInitialRepetitionsCardNotIsSquareTwelveMulAddOneEightMulAddOne

end MathlibExtTest.NumberTheory
