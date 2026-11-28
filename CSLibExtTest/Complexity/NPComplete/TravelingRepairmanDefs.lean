/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TravelingRepairmanDefs

namespace MetaMathlibExt.Complexity.NPComplete.TravelingRepairman

open MetaMathlibExt.BitstringEncoding

/-- Three locations at positions `0`, `1` and `3` on a line, starting at `0`, with bound `K`. -/
private abbrev line (K : ℕ) : TravelingRepairmanInstance :=
  (3, [[0, 1, 3], [1, 0, 2], [3, 2, 0]], 0, K)

private theorem line_wellFormed (K : ℕ) : WellFormed (line K) := by
  unfold WellFormed dist; dsimp only; decide

/-- The route `0, 1, 2` reaches its locations at times `0`, `1`, `3`: total latency `4`. -/
example : totalLatency (line 4) [0, 1, 2] = 4 := by decide

/-- The route `0, 2, 1` reaches them at times `0`, `3`, `5`: total latency `8`, the sum of
its prefix lengths rather than its length `5`. -/
example : totalLatency (line 4) [0, 2, 1] = 8 ∧ routeLength (line 4) [0, 2, 1] = 5 := by decide

/-- The route `0, 1, 2` meets the bound `4`. -/
private theorem line_four_feasible : TravelingRepairmanFeasible (line 4) :=
  ⟨[0, 1, 2], by decide, rfl, by decide⟩

/-- A permutation of `0, 1, 2` is a list `[a, b, c]` of distinct locations below `3`. -/
private theorem route_three {route : List ℕ} (h : route.Perm (List.range 3)) :
    ∃ a < 3, ∃ b < 3, ∃ c < 3, route = [a, b, c] ∧ [a, b, c].Nodup := by
  have hlen := h.length_eq
  have hlt : ∀ x ∈ route, x < 3 := fun x hx => List.mem_range.mp (h.mem_iff.mp hx)
  have hnd : route.Nodup := h.nodup_iff.mpr List.nodup_range
  rcases route with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨a, hlt a (by simp), b, hlt b (by simp), c, hlt c (by simp), rfl, hnd⟩

/-- No route from `0` has total latency `3`: the best one, `0, 1, 2`, has `4`. -/
private theorem line_three_infeasible : ¬ TravelingRepairmanFeasible (line 3) := by
  rintro ⟨route, hperm, hhead, hle⟩
  obtain ⟨a, ha, b, hb, c, hc, rfl, hnd⟩ := route_three hperm
  have key : ∀ a < 3, ∀ b < 3, ∀ c < 3, [a, b, c].Nodup → [a, b, c].head? = some 0 →
      3 < totalLatency (line 3) [a, b, c] := by decide
  exact absurd hle (Nat.not_le.mpr (key a ha b hb c hc hnd hhead))

/-- The route must start at `s`: `1, 0, 2` is a permutation of the locations with total
latency `5`, but it does not start at `0`. -/
example : totalLatency (line 5) [1, 0, 2] = 5 ∧ [1, 0, 2].head? ≠ some (line 5).2.2.1 := by
  decide

/-- The starting location `3` is not a location: malformed, and no permutation of `0, 1, 2`
starts there. -/
private theorem badStart_malformed :
    ¬ WellFormed ((3, [[0, 1, 3], [1, 0, 2], [3, 2, 0]], 3, 10) : TravelingRepairmanInstance) := by
  unfold WellFormed; decide

/-- Distances violating the triangle inequality are malformed (`t[0, 2] = 5 > 1 + 2`),
although the route `0, 1, 2` still has total latency `4`. -/
private abbrev nonMetric : TravelingRepairmanInstance :=
  (3, [[0, 1, 5], [1, 0, 2], [5, 2, 0]], 0, 4)

private theorem nonMetric_malformed : ¬ WellFormed nonMetric := by
  unfold WellFormed dist; decide

private theorem nonMetric_feasible : TravelingRepairmanFeasible nonMetric :=
  ⟨[0, 1, 2], by decide, rfl, by decide⟩

/-- The decision problem accepts the encoding of `line 4`. -/
example : travelingRepairmanDec (bitEncode (line 4)) = true := by
  simp [travelingRepairmanDec, line_wellFormed, line_four_feasible]

/-- It rejects the encoding of the well-formed but infeasible `line 3`. -/
example : travelingRepairmanDec (bitEncode (line 3)) = false := by
  simp [travelingRepairmanDec, line_three_infeasible]

/-- It rejects the feasible but non-metric instance, and the one with an invalid start. -/
example : TravelingRepairmanFeasible nonMetric ∧
    travelingRepairmanDec (bitEncode nonMetric) = false ∧
    travelingRepairmanDec (bitEncode
      ((3, [[0, 1, 3], [1, 0, 2], [3, 2, 0]], 3, 10) : TravelingRepairmanInstance)) = false :=
  ⟨nonMetric_feasible, by simp [travelingRepairmanDec, nonMetric_malformed],
    by simp [travelingRepairmanDec, badStart_malformed]⟩

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : travelingRepairmanDec [true] = false := by
  have h : bitDecode (α := TravelingRepairmanInstance) [true] = none := rfl
  simp [travelingRepairmanDec, h]

end MetaMathlibExt.Complexity.NPComplete.TravelingRepairman
