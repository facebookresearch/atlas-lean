/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MetricBottleneckWanderingSalespersonDefs
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance dist)

private theorem dec_bitEncode (i : MetricBottleneckWanderingSalespersonInstance) :
    metricBottleneckWanderingSalespersonDec (bitEncode i) = true ↔
      WellFormed i ∧ MetricBottleneckWanderingSalespersonFeasible i := by
  simp [metricBottleneckWanderingSalespersonDec, bitDecode_bitEncode]

/-- Three cities on a line (`d(0, 1) = d(1, 2) = 1`, `d(0, 2) = 2`), from `0` to `2` with
bottleneck `K = 1`: the path `0, 1, 2`. -/
example :
    metricBottleneckWanderingSalespersonDec
      (bitEncode (((3, [[0, 1, 2], [1, 0, 1], [2, 1, 0]], 1), 0, 2) :
        MetricBottleneckWanderingSalespersonInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed BottleneckTravelingSalesman.WellFormed dist; decide,
    [0, 1, 2], List.Perm.refl _, rfl, rfl, ?_⟩
  intro j hj
  have hj2 : j < 2 := by simp at hj; omega
  match j, hj2 with
  | 0, _ => decide
  | 1, _ => decide

/-- The same cities from `0` to `1`: the only path is `0, 2, 1`, whose first step has length
`2 > K = 1`. -/
example :
    metricBottleneckWanderingSalespersonDec
      (bitEncode (((3, [[0, 1, 2], [1, 0, 1], [2, 1, 0]], 1), 0, 1) :
        MetricBottleneckWanderingSalespersonInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, path, hperm, hhead, hlast, hstep⟩
  have hmem := List.mem_permutations'.2 hperm
  have key : ∀ p ∈ (List.range 3).permutations', p.head? = some 0 → p.getLast? = some 1 →
      ¬ (dist [[0, 1, 2], [1, 0, 1], [2, 1, 0]] (p.getD 0 0) (p.getD 1 0) ≤ 1 ∧
        dist [[0, 1, 2], [1, 0, 1], [2, 1, 0]] (p.getD 1 0) (p.getD 2 0) ≤ 1) := by
    unfold dist; decide
  exact key path hmem hhead hlast ⟨hstep 0 (by decide), hstep 1 (by decide)⟩

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MetricBottleneckWanderingSalespersonInstance) bits = none) :
    metricBottleneckWanderingSalespersonDec bits = false := by
  simp [metricBottleneckWanderingSalespersonDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : metricBottleneckWanderingSalespersonDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson
