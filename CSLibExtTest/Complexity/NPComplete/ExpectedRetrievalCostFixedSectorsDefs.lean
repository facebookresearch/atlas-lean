/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectorsDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectors

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCost (toRat retrievalCost)

private theorem accepts_encoding (m : ℕ) (i : ExpectedRetrievalCostFixedSectorsInstance) :
    expectedRetrievalCostFixedSectorsDec m (bitEncode i) = true ↔
      WellFormed i ∧ ExpectedRetrievalCostFixedSectorsFeasible m i := by
  simp [expectedRetrievalCostFixedSectorsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every number of sectors. -/
example (m : ℕ) : expectedRetrievalCostFixedSectorsDec m [true] = false := by
  have h : bitDecode (α := ExpectedRetrievalCostFixedSectorsInstance) [true] = none := rfl
  simp [expectedRetrievalCostFixedSectorsDec, h]

/-- Two records of probability `1/2` each, with bound `K`. -/
private abbrev halves (K : ℕ × ℕ) : ExpectedRetrievalCostFixedSectorsInstance :=
  ([(1, 2), (1, 2)], K)

private theorem wellFormed_halves (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    WellFormed (halves (a, b)) := by
  refine ⟨?_, ?_, hb, ha⟩
  · show ∀ q ∈ ([(1, 2), (1, 2)] : List (ℕ × ℕ)), 0 < q.2 ∧ q.1 ≤ q.2
    decide
  · show (([(1, 2), (1, 2)] : List (ℕ × ℕ)).map toRat).sum = 1
    decide +kernel

/-- With two sectors, one record per sector costs `1/4 + 1/4 = 1/2`: only the latency `1` of a
sector to itself contributes, since the latency between the two sectors is `0` both ways. -/
example : expectedRetrievalCostFixedSectorsDec 2 (bitEncode (halves (1, 2))) = true := by
  refine (accepts_encoding _ _).2 ⟨wellFormed_halves 1 2 (by decide) (by decide),
    fun r => r, fun b => ⟨b, rfl⟩, ?_⟩
  decide +kernel

/-- With two sectors and bound `1/4`, every allocation costs at least `1/2`. -/
example : expectedRetrievalCostFixedSectorsDec 2 (bitEncode (halves (1, 4))) = false := by
  have h : ¬ ExpectedRetrievalCostFixedSectorsFeasible 2 (halves (1, 4)) := by
    rintro ⟨f, -, hf⟩
    revert f
    decide +kernel
  simpa [expectedRetrievalCostFixedSectorsDec, bitDecode_bitEncode] using fun _ => h

/-- With three sectors, two records cannot leave every sector nonempty. -/
example : expectedRetrievalCostFixedSectorsDec 3 (bitEncode (halves (1, 1))) = false := by
  have h : ¬ ExpectedRetrievalCostFixedSectorsFeasible 3 (halves (1, 1)) := by
    rintro ⟨f, hsurj, -⟩
    have := Fintype.card_le_of_surjective f hsurj
    simp at this
  simpa [expectedRetrievalCostFixedSectorsDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.ExpectedRetrievalCostFixedSectors
