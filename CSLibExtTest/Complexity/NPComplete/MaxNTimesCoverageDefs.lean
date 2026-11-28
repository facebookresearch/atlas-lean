/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaxNTimesCoverageDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaxNTimesCoverage

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : Instance) :
    maxNTimesCoverageDec (bitEncode i) = true ↔ WellFormed i ∧ Feasible i := by
  simp [maxNTimesCoverageDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := Instance) bits = none) :
    maxNTimesCoverageDec bits = false := by
  simp [maxNTimesCoverageDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : maxNTimesCoverageDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Overlays `110` and `111` cover elements `0` and `1` twice, total weight `2`. -/
example :
    maxNTimesCoverageDec (bitEncode
      ((2, [[1, 1, 0], [1, 0, 1], [1, 1, 1]], [1, 1, 1], 2, 2) : Instance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, [[1, 1, 0], [1, 1, 1]], by decide, by decide,
    by decide⟩

/-- With a single overlay of `0/1` entries, no element is covered twice. -/
example :
    maxNTimesCoverageDec (bitEncode
      ((2, [[1, 1, 0], [1, 0, 1], [1, 1, 1]], [1, 1, 1], 1, 1) : Instance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, sub, hsub, hlen, hcov⟩
  rcases sub with _ | ⟨r, _ | ⟨s, sub⟩⟩
  · revert hcov; decide
  · have hr : r ∈ [[1, 1, 0], [1, 0, 1], [1, 1, 1]] := hsub.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> revert hcov <;> decide
  · simp at hlen

/-- A row whose length differs from the number of weights is malformed. -/
example :
    maxNTimesCoverageDec (bitEncode ((1, [[1]], [1, 1], 1, 0) : Instance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h [1] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.MaxNTimesCoverage
