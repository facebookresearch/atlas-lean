/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaximumNashSocialWelfareDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaximumNashSocialWelfare

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MaximumNashSocialWelfareInstance) :
    maximumNashSocialWelfareDec (bitEncode i) = true ↔
      WellFormed i ∧ MaximumNashSocialWelfareFeasible i := by
  simp [maximumNashSocialWelfareDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MaximumNashSocialWelfareInstance) bits = none) :
    maximumNashSocialWelfareDec bits = false := by
  simp [maximumNashSocialWelfareDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : maximumNashSocialWelfareDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Two agents valuing two goods `[2, 1]` and `[1, 3]`: giving good `0` to agent `0` and good
`1` to agent `1` has Nash social welfare `2 * 3 = 6`. -/
example :
    maximumNashSocialWelfareDec (bitEncode
      ((2, [[2, 1], [1, 3]], 6) : MaximumNashSocialWelfareInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun g => ⟨g.val, g.isLt⟩, ?_⟩
  unfold utility
  decide

/-- No allocation of the two goods reaches Nash social welfare `7`. -/
example :
    maximumNashSocialWelfareDec (bitEncode
      ((2, [[2, 1], [1, 3]], 7) : MaximumNashSocialWelfareInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, f, hf⟩
  revert f hf
  unfold utility
  decide

/-- An instance with no agents is malformed, although its empty product `1` meets bound `1`. -/
example :
    maximumNashSocialWelfareDec (bitEncode
      ((0, [], 1) : MaximumNashSocialWelfareInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨h, -⟩, -⟩
  exact absurd h (by decide)

/-- The agentless instance does meet its bound: the empty product is `1`. -/
example : MaximumNashSocialWelfareFeasible ((0, [], 1) : MaximumNashSocialWelfareInstance) :=
  ⟨fun g => g.elim0, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.MaximumNashSocialWelfare
