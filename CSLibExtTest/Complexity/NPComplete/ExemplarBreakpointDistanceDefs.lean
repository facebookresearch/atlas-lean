/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExemplarBreakpointDistanceDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ExemplarBreakpointDistanceInstance) :
    exemplarBreakpointDistanceDec (bitEncode i) = true ↔
      WellFormed i ∧ ExemplarBreakpointDistanceFeasible i := by
  simp [exemplarBreakpointDistanceDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : exemplarBreakpointDistanceDec [true] = false := by
  have h : bitDecode (α := ExemplarBreakpointDistanceInstance) [true] = none := rfl
  simp [exemplarBreakpointDistanceDec, h]

/-- `G = +1 +2 +1` repeats family `1`; dropping its last gene gives the exemplar `+1 +2`, which
equals `H = +1 +2`, at breakpoint distance `0`. -/
example : exemplarBreakpointDistanceDec (bitEncode
    (([(1, true), (2, true), (1, true)], [(1, true), (2, true)], 0) :
      ExemplarBreakpointDistanceInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, [(1, true), (2, true)],
    [(1, true), (2, true)], ⟨by decide, by decide, by decide⟩, ⟨List.Sublist.refl _, by decide,
      by decide⟩, by decide⟩

/-- An exemplar of a genome whose families occur once each is the genome itself. -/
private theorem exemplar_eq {X x : List (ℕ × Bool)} (hX : (X.map Prod.fst).Nodup)
    (h : IsExemplar X x) : x = X := by
  obtain ⟨hs, hn, hall⟩ := h
  have := (List.subperm_of_subset hX hall).length_le
  simp only [List.length_map] at this
  exact hs.eq_of_length_le this

/-- `G = +1 +2` and `H = +2 +1`: each family occurs once, so the only exemplars are the genomes,
which differ in their adjacency and at both ends, for distance `3 > 2`. -/
example : exemplarBreakpointDistanceDec (bitEncode
    (([(1, true), (2, true)], [(2, true), (1, true)], 2) :
      ExemplarBreakpointDistanceInstance)) = false := by
  cases h : exemplarBreakpointDistanceDec (bitEncode
      (([(1, true), (2, true)], [(2, true), (1, true)], 2) :
        ExemplarBreakpointDistanceInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, g, k, hg, hk, hd⟩ := (accepts_encoding _).1 h
    obtain rfl := exemplar_eq (by decide) hg
    obtain rfl := exemplar_eq (by decide) hk
    exact absurd hd (by decide)

end MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance
