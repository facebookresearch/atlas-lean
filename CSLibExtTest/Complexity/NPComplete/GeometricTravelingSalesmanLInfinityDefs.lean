/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinityDefs
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinity

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (GeometricTravelingSalesmanInstance WellFormed point toInt)

private theorem dec_bitEncode (i : GeometricTravelingSalesmanInstance) :
    geometricTravelingSalesmanLInfinityDec (bitEncode i) = true ↔
      WellFormed i ∧ GeometricTravelingSalesmanLInfinityFeasible i := by
  simp [geometricTravelingSalesmanLInfinityDec, bitDecode_bitEncode]

/-- A list of `n` entries containing every city `v < n` is a permutation of the cities. -/
private theorem perm_range_of_tour {n : ℕ} {tour : List ℕ}
    (hlen : tour.length = n) (hall : ∀ v < n, v ∈ tour) : tour.Perm (List.range n) :=
  ((List.subperm_of_subset List.nodup_range fun v hv => hall v (List.mem_range.1 hv)).perm_of_length_le
    (by simp [hlen])).symm

/-- The points `(0, 0)`, `(1, 1)`, `(2, 0)` have `L∞` distances `1`, `1`, `2`; the tour in
input order has length `4 ≤ B = 4`. -/
example :
    geometricTravelingSalesmanLInfinityDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (1, 0)), ((2, 0), (0, 0))], 4) :
        GeometricTravelingSalesmanInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed point toInt; decide, [0, 1, 2], ?_⟩
  unfold toTspInstance Tsp.TourLength chebyshevDist point toInt
  decide

/-- The same three points with `B = 3`: every tour has `L∞` length `4`. -/
example :
    geometricTravelingSalesmanLInfinityDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (1, 0)), ((2, 0), (0, 0))], 3) :
        GeometricTravelingSalesmanInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, tour, -, hlen, hall, hle⟩
  have hmem := List.mem_permutations'.2 (perm_range_of_tour hlen hall)
  revert hle
  generalize tour = t at hmem
  revert t
  unfold toTspInstance Tsp.TourLength chebyshevDist point toInt
  decide

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricTravelingSalesmanInstance) bits = none) :
    geometricTravelingSalesmanLInfinityDec bits = false := by
  simp [geometricTravelingSalesmanLInfinityDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : geometricTravelingSalesmanLInfinityDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinity
