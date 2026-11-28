/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MetricTravelingKSalespersonDefs
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.MetricTravelingKSalesperson

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open TravelingRepairman (routeLength)

private theorem dec_bitEncode (i : MetricTravelingKSalespersonInstance) :
    metricTravelingKSalespersonDec (bitEncode i) = true ↔
      WellFormed i ∧ MetricTravelingKSalespersonFeasible i := by
  simp [metricTravelingKSalespersonDec, bitDecode_bitEncode]

/-- A star metric around city `0` (`d(0, 1) = d(0, 2) = 1`, `d(1, 2) = 2`) with `k = 2` and
`K = 2`: the subtours `0, 1` and `0, 2` each have closed length `2`. -/
example :
    metricTravelingKSalespersonDec
      (bitEncode ((3, [[0, 1, 1], [1, 0, 2], [1, 2, 0]], 0, 2, 2) :
        MetricTravelingKSalespersonInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed toMetric TravelingRepairman.WellFormed TravelingRepairman.dist; decide,
    [[0, 1], [0, 2]], ?_⟩
  unfold toMetric routeLength TravelingRepairman.dist
  decide

/-- A list of distinct cities below `n` that contains every city is a permutation of them. -/
private theorem perm_range {n : ℕ} {t : List ℕ} (hnd : t.Nodup) (hlt : ∀ c ∈ t, c < n)
    (hall : ∀ c < n, c ∈ t) : t.Perm (List.range n) :=
  (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun c =>
    ⟨fun h => List.mem_range.2 (hlt c h), fun h => hall c (List.mem_range.1 h)⟩

/-- The same metric with a single subtour (`k = 1`): it must visit both `1` and `2`, and every
such closed route from `0` has length `4 > K = 2`. -/
example :
    metricTravelingKSalespersonDec
      (bitEncode ((3, [[0, 1, 1], [1, 0, 2], [1, 2, 0]], 0, 1, 2) :
        MetricTravelingKSalespersonInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, tours, hlen, htours, hcover⟩
  obtain ⟨t, ht, -⟩ := hcover 0 (by decide)
  have hsingle : ∀ c < 3, c ∈ t := by
    intro c hc
    obtain ⟨t', ht', hc'⟩ := hcover c hc
    match tours, hlen, ht, ht' with
    | [_], _, ht, ht' =>
      simp only [List.mem_singleton] at ht ht'
      exact ht ▸ ht' ▸ hc'
  obtain ⟨hhead, hnd, hlt, hroute⟩ := htours t ht
  have hmem := List.mem_permutations'.2 (perm_range hnd hlt hsingle)
  revert hhead hroute
  generalize t = u at hmem
  revert u
  unfold toMetric routeLength TravelingRepairman.dist
  decide

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MetricTravelingKSalespersonInstance) bits = none) :
    metricTravelingKSalespersonDec bits = false := by
  simp [metricTravelingKSalespersonDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : metricTravelingKSalespersonDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.MetricTravelingKSalesperson
