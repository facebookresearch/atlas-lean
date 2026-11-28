/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EuclideanTwoMeansDefs

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanTwoMeans

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open QuadraticProgramming (RatCode)

private theorem accepts_encoding (i : EuclideanTwoMeansInstance) :
    euclideanTwoMeansDec (bitEncode i) = true ↔
      WellFormed i ∧ EuclideanTwoMeansFeasible i := by
  simp [euclideanTwoMeansDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : euclideanTwoMeansDec [true] = false := by
  have h : bitDecode (α := EuclideanTwoMeansInstance) [true] = none := rfl
  simp [euclideanTwoMeansDec, h]

/-- Three points on a line, at `0`, `2` and `4`, with bound `B`. -/
private abbrev line (B : RatCode) : EuclideanTwoMeansInstance :=
  (1, [[((0, 0), 1)], [((2, 0), 1)], [((4, 0), 1)]], B)

/-- Bound `2`: the clusters `{0}` and `{2, 4}` have costs `0` and `1 + 1`. -/
example : euclideanTwoMeansDec (bitEncode (line ((2, 0), 1))) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    Finset.univ.filter fun x => x.1 = 0, by decide, by decide, ?_⟩
  decide +kernel

/-- Bound `1`: the three splits cost `2`, `2` and `8`. -/
example : euclideanTwoMeansDec (bitEncode (line ((1, 0), 1))) = false := by
  have h : ¬ EuclideanTwoMeansFeasible (line ((1, 0), 1)) := by
    unfold EuclideanTwoMeansFeasible
    decide +kernel
  simp [euclideanTwoMeansDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.EuclideanTwoMeans
