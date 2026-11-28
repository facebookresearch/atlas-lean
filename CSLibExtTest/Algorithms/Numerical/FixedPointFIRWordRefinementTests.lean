/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Numerical.FixedPointFIRWordRefinement
public meta import CSLibExt.Algorithms.Numerical.FixedPointFIRWordRefinement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Fixed-point FIR word refinement examples -/

open MathlibExt.Analysis.Numerical
open CSLibExt.Algorithms.Numerical.FixedPointFIR
open CSLibExt.Algorithms.Numerical.FixedPointFIRWordRefinement

/-! ### Exhaustive step agreement at small widths -/

-- Every accumulator, flag and operand pair at width 2, scale `2 ^ 1`.
example :
    (List.range 4).all (fun a => (List.range 4).all (fun b => (List.range 4).all
      (fun c => [false, true].all (fun f =>
        (wordStep 2 1 (BitVec.ofNat 2 a) f (BitVec.ofNat 2 b) (BitVec.ofNat 2 c)).1.toInt
            == (firStep 1 (SaturatingRoundHalfUp.signedMinCode 2)
              (SaturatingRoundHalfUp.signedMaxCode 2) (BitVec.ofNat 2 a).toInt f
              (BitVec.ofNat 2 b).toInt (BitVec.ofNat 2 c).toInt).1 &&
          (wordStep 2 1 (BitVec.ofNat 2 a) f (BitVec.ofNat 2 b) (BitVec.ofNat 2 c)).2
            == (firStep 1 (SaturatingRoundHalfUp.signedMinCode 2)
              (SaturatingRoundHalfUp.signedMaxCode 2) (BitVec.ofNat 2 a).toInt f
              (BitVec.ofNat 2 b).toInt (BitVec.ofNat 2 c).toInt).2)))) = true := by
  decide

/-! ### Width 4, scale `2 ^ 2`

Taps `[2, -2, 3]`, inputs `[1, 1, -2]`. The products `2, -2, -6` are the
ties `0.5, -0.5, -1.5`, rounded half up to `1, 0, -1`; the partial sums
are `1, 1, 0` and nothing overflows. -/

example :
    (wordRoundHalfUpShift 4 2 (wordProduct 4 2 2#4 1#4)).toInt = 1 ∧
      (wordRoundHalfUpShift 4 2 (wordProduct 4 2 (BitVec.ofInt 4 (-2)) 1#4)).toInt = 0 ∧
      (wordRoundHalfUpShift 4 2 (wordProduct 4 2 3#4 (BitVec.ofInt 4 (-2)))).toInt = -1 := by
  decide

example :
    (wordCode 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4] ![1#4, 1#4, BitVec.ofInt 4 (-2)]).toInt = 0 ∧
      wordOverflow 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4]
        ![1#4, 1#4, BitVec.ofInt 4 (-2)] = false := by
  decide

example :
    (wordCode 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4] ![1#4, 1#4, BitVec.ofInt 4 (-2)]).toInt
        = firCode 2 (SaturatingRoundHalfUp.signedMinCode 4)
            (SaturatingRoundHalfUp.signedMaxCode 4) ![2, -2, 3] ![1, 1, -2] ∧
      wordOverflow 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4] ![1#4, 1#4, BitVec.ofInt 4 (-2)]
        = firOverflow 2 (SaturatingRoundHalfUp.signedMinCode 4)
            (SaturatingRoundHalfUp.signedMaxCode 4) ![2, -2, 3] ![1, 1, -2] := by
  decide

-- The decoded output `0` is within the error bound of the ideal output `-3/8`,
-- obtained by instantiating `wordFir_correct`.
example :
    |decodeWord 2 (wordCode 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4]
        ![1#4, 1#4, BitVec.ofInt 4 (-2)])
        - OrderedDotProductError.outputIdeal 3 ![1/2, -1/2, 3/4] ![1/4, 1/4, -1/2]|
      ≤ ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) * (∑ k : Fin 3, |(![1/2, -1/2, 3/4] : Fin 3 → ℝ) k|)
        + ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) * (∑ k : Fin 3, |(![1/4, 1/4, -1/2] : Fin 3 → ℝ) k|)
        + ((3 : ℕ) : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2))
        + ((3 : ℕ) : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) := by
  have e1 : (1#4).toInt = 1 := by decide
  have e2 : (2#4).toInt = 2 := by decide
  have e3 : (3#4).toInt = 3 := by decide
  have em : (BitVec.ofInt 4 (-2)).toInt = -2 := by decide
  have hno : wordOverflow 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4]
      ![1#4, 1#4, BitVec.ofInt 4 (-2)] = false := by
    decide
  refine (wordFir_correct 2 4 3 (by norm_num) _ _ _ _ ?_ ?_ hno).2
  · intro k
    fin_cases k <;> norm_num [decodeWord, decode, e1, em]
  · intro k
    fin_cases k <;> norm_num [decodeWord, decode, e2, e3, em]

/-! ### Width 4, overflowing trace

The second product `7 * 7 / 4` rounds to `12 > 7`: the partial sum
saturates to `7` and the flag is set, exactly as in the integer fold. -/

example :
    (wordCode 4 2 ![BitVec.ofInt 4 (-3), 7#4] ![2#4, 7#4]).toInt = 7 ∧
      wordOverflow 4 2 ![BitVec.ofInt 4 (-3), 7#4] ![2#4, 7#4] = true := by
  decide

example :
    (wordCode 4 2 ![BitVec.ofInt 4 (-3), 7#4] ![2#4, 7#4]).toInt
        = firCode 2 (SaturatingRoundHalfUp.signedMinCode 4)
            (SaturatingRoundHalfUp.signedMaxCode 4) ![-3, 7] ![2, 7] ∧
      wordOverflow 4 2 ![BitVec.ofInt 4 (-3), 7#4] ![2#4, 7#4]
        = firOverflow 2 (SaturatingRoundHalfUp.signedMinCode 4)
            (SaturatingRoundHalfUp.signedMaxCode 4) ![-3, 7] ![2, 7] := by
  decide

/-! ### Width 8, scale `2 ^ 4`

Taps `[24, -40, 8, -8]`, inputs `[-8, 20, 2, -2]`: the rounded products
are `-12, -50, 1, 1` and the output is `-60`, with no overflow. -/

example :
    (wordCode 8 4 ![24#8, BitVec.ofInt 8 (-40), 8#8, BitVec.ofInt 8 (-8)]
        ![BitVec.ofInt 8 (-8), 20#8, 2#8, BitVec.ofInt 8 (-2)]).toInt = -60 ∧
      wordOverflow 8 4 ![24#8, BitVec.ofInt 8 (-40), 8#8, BitVec.ofInt 8 (-8)]
        ![BitVec.ofInt 8 (-8), 20#8, 2#8, BitVec.ofInt 8 (-2)] = false := by
  decide

example :
    (wordCode 8 4 ![24#8, BitVec.ofInt 8 (-40), 8#8, BitVec.ofInt 8 (-8)]
        ![BitVec.ofInt 8 (-8), 20#8, 2#8, BitVec.ofInt 8 (-2)]).toInt
        = firCode 4 (SaturatingRoundHalfUp.signedMinCode 8)
            (SaturatingRoundHalfUp.signedMaxCode 8) ![24, -40, 8, -8] ![-8, 20, 2, -2] ∧
      wordOverflow 8 4 ![24#8, BitVec.ofInt 8 (-40), 8#8, BitVec.ofInt 8 (-8)]
          ![BitVec.ofInt 8 (-8), 20#8, 2#8, BitVec.ofInt 8 (-2)]
        = firOverflow 4 (SaturatingRoundHalfUp.signedMinCode 8)
            (SaturatingRoundHalfUp.signedMaxCode 8) ![24, -40, 8, -8] ![-8, 20, 2, -2] := by
  decide

-- Ties: `-24 / 16 = -1.5` rounds half up to `-1`, and `24 / 16 = 1.5` to `2`.
example :
    (wordRoundHalfUpShift 8 4 (wordProduct 8 4 (BitVec.ofInt 8 (-3)) 8#8)).toInt = -1 ∧
      (wordRoundHalfUpShift 8 4 (wordProduct 8 4 3#8 8#8)).toInt = 2 := by
  decide

/-! ### Width 8, overflowing trace

`-128 * 127 / 16` rounds to `-1016 < -128`: the output saturates to
`-128` and the flag is set, as in the integer fold. -/

example :
    (wordCode 8 4 ![BitVec.intMin 8] ![BitVec.intMax 8]).toInt = -128 ∧
      wordOverflow 8 4 ![BitVec.intMin 8] ![BitVec.intMax 8] = true := by
  decide

example :
    (wordCode 8 4 ![BitVec.intMin 8] ![BitVec.intMax 8]).toInt
        = firCode 4 (SaturatingRoundHalfUp.signedMinCode 8)
            (SaturatingRoundHalfUp.signedMaxCode 8) ![-128] ![127] ∧
      wordOverflow 8 4 ![BitVec.intMin 8] ![BitVec.intMax 8]
        = firOverflow 4 (SaturatingRoundHalfUp.signedMinCode 8)
            (SaturatingRoundHalfUp.signedMaxCode 8) ![-128] ![127] := by
  decide

/-! ### Rounding near the top of the intermediate range

At width `1`, scale `2 ^ 1`, the intermediate width is `4` and its greatest
word is `7`. Adding the offset `1` to `7` needs a fifth bit; `7 / 2 = 3.5`
rounds half up to `4`, not to the wrapped `-8 / 2 = -4`. -/

example :
    (wordRoundHalfUpShift 1 1 (BitVec.intMax (wideWidth 1 1))).toInt = 4 ∧
      roundHalfUpShift 1 (BitVec.intMax (wideWidth 1 1)).toInt = 4 := by
  decide

-- Every intermediate word at width 1, scales `2 ^ 0` through `2 ^ 2`.
example :
    (List.range (2 ^ wideWidth 1 0)).all (fun k =>
      (wordRoundHalfUpShift 1 0 (BitVec.ofNat (wideWidth 1 0) k)).toInt
        == roundHalfUpShift 0 (BitVec.ofNat (wideWidth 1 0) k).toInt) &&
    (List.range (2 ^ wideWidth 1 1)).all (fun k =>
      (wordRoundHalfUpShift 1 1 (BitVec.ofNat (wideWidth 1 1) k)).toInt
        == roundHalfUpShift 1 (BitVec.ofNat (wideWidth 1 1) k).toInt) &&
    (List.range (2 ^ wideWidth 1 2)).all (fun k =>
      (wordRoundHalfUpShift 1 2 (BitVec.ofNat (wideWidth 1 2) k)).toInt
        == roundHalfUpShift 2 (BitVec.ofNat (wideWidth 1 2) k).toInt) = true := by
  decide

/-! ### Saturation and the core signed-overflow predicate -/

example :
    (saturateWord 4 2 (BitVec.ofInt (wideWidth 4 2) 100)).toInt = 7 ∧
      (saturateWord 4 2 (BitVec.ofInt (wideWidth 4 2) (-100))).toInt = -8 ∧
      (saturateWord 4 2 (BitVec.ofInt (wideWidth 4 2) (-5))).toInt = -5 := by
  decide

-- `5 + 3` overflows width 4; the partial-sum range test agrees with `saddOverflow`.
example :
    outOfRange 4 2 (widen 4 2 5#4 + BitVec.ofInt (wideWidth 4 2) 3) = true ∧
      (5#4).saddOverflow 3#4 = true := by
  decide
