/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GreeneSellersInitialRepetitionsCardNotIsSquareTwelveMulAddOneEightMulAddOne
import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete simultaneous-nonresidue counts

We apply the counting theorem at the primes $2$, $3$, $5$, $7$, and $11$.
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

end GreeneSellersInitialRepetitionsCardNotIsSquareTwelveMulAddOneEightMulAddOne

end MathlibExtTest.NumberTheory
