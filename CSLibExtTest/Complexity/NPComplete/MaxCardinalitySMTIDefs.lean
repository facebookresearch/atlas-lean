/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaxCardinalitySMTIDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaxCardinalitySMTI

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MaxCardinalitySMTIInstance) :
    maxCardinalitySMTIDec (bitEncode i) = true ↔
      WellFormed i ∧ MaxCardinalitySMTIFeasible i := by
  simp [maxCardinalitySMTIDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MaxCardinalitySMTIInstance) bits = none) :
    maxCardinalitySMTIDec bits = false := by
  simp [maxCardinalitySMTIDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : maxCardinalitySMTIDec [true] = false :=
  rejects_undecodable [true] rfl

-- Stability checks quantify over every pair and partner, which exceeds the default instance
-- size bound for `decide`.
set_option synthInstance.maxSize 1024

/-- Man `0` prefers woman `0` to woman `1`, man `1` accepts only woman `0`, woman `0` prefers
man `1` to man `0`, and woman `1` accepts only man `0`: the perfect matching
`{(0, 1), (1, 0)}` is stable. -/
example :
    maxCardinalitySMTIDec (bitEncode
      ((2, [[[0], [1]], [[0]]], [[[1], [0]], [[0]]], 2) : MaxCardinalitySMTIInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {(0, 1), (1, 0)}, ?_, ?_, by decide⟩
  · unfold IsMatching
    refine ⟨?_, by decide, by decide⟩
    unfold manList womanList Acceptable
    decide
  · unfold Blocks StrictlyPrefers tieIndex manList womanList Acceptable
    decide

/-- When man `0` and woman `0` rank each other first, every stable matching contains
`(0, 0)`, so none has two pairs although the matching `{(0, 1), (1, 0)}` does. -/
example :
    maxCardinalitySMTIDec (bitEncode
      ((2, [[[0], [1]], [[0]]], [[[0], [1]], [[0]]], 2) : MaxCardinalitySMTIInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, M, hM, hstable, hcard⟩
  revert M
  unfold IsMatching Blocks StrictlyPrefers tieIndex manList womanList Acceptable
  decide

/-- A man listing a woman twice is malformed. -/
example :
    maxCardinalitySMTIDec (bitEncode
      ((1, [[[0], [0]]], [[[0]]], 1) : MaxCardinalitySMTIInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, h, -⟩, -⟩
  exact absurd (h [[0], [0]] (by simp)).1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.MaxCardinalitySMTI
