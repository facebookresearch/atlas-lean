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

-- The decoded output `0` is within the error bound of the ideal output `-3/8`.
example :
    |decodeWord 2 (wordCode 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4]
        ![1#4, 1#4, BitVec.ofInt 4 (-2)])
        - OrderedDotProductError.outputIdeal 3 ![1/2, -1/2, 3/4] ![1/4, 1/4, -1/2]|
      ≤ ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) * (∑ k : Fin 3, |(![1/2, -1/2, 3/4] : Fin 3 → ℝ) k|)
        + ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) * (∑ k : Fin 3, |(![1/4, 1/4, -1/2] : Fin 3 → ℝ) k|)
        + ((3 : ℕ) : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2))
        + ((3 : ℕ) : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2))
        + ((3 : ℕ) : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ 2)) := by
  have hc : (wordCode 4 2 ![2#4, BitVec.ofInt 4 (-2), 3#4]
      ![1#4, 1#4, BitVec.ofInt 4 (-2)]).toInt = 0 := by
    decide
  simp only [decodeWord, decode, hc, OrderedDotProductError.outputIdeal, Fin.sum_univ_three]
  norm_num [abs_of_pos, abs_of_neg]

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
