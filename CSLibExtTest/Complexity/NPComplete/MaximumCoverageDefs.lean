/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaximumCoverageDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCoverage

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MaximumCoverageInstance) :
    maximumCoverageDec (bitEncode i) = true ↔ WellFormed i ∧ MaximumCoverageFeasible i := by
  simp [maximumCoverageDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MaximumCoverageInstance) bits = none) :
    maximumCoverageDec bits = false := by
  simp [maximumCoverageDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : maximumCoverageDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The subsets `{0, 1}` and `{2, 3}` together cover all four elements. -/
example :
    maximumCoverageDec (bitEncode
      ((4, [[0, 1], [1, 2], [2, 3]], 2, 4) : MaximumCoverageInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [[0, 1], [2, 3]], by decide, by decide,
    [0, 1, 2, 3], by decide, by decide, ?_⟩
  decide

/-- One two-element subset cannot cover three distinct elements. -/
example :
    maximumCoverageDec (bitEncode
      ((4, [[0, 1], [1, 2], [2, 3]], 1, 3) : MaximumCoverageInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, T, hsub, hlen, covered, hnd, hcount, hcov⟩
  rcases T with _ | ⟨s, _ | ⟨t, T⟩⟩
  · rcases covered with _ | ⟨x, covered⟩
    · simp at hcount
    · simpa using (hcov x (by simp)).2
  · have hs : s ∈ [[0, 1], [1, 2], [2, 3]] := hsub.subset (by simp)
    have hsubset : covered ⊆ s := by
      intro x hx
      simpa using (hcov x hx).2
    have := hnd.length_le_of_subset hsubset
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp at this hcount <;> omega
  · simp at hlen

/-- A subset with a repeated element is malformed. -/
example :
    maximumCoverageDec (bitEncode ((2, [[0, 0]], 1, 1) : MaximumCoverageInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h [0, 0] (by simp)).1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.MaximumCoverage
