/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MetricTravelingSalespersonDefs

namespace MetaMathlibExt.Complexity.NPComplete.MetricTravelingSalesperson

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Tsp (TspInstance)

example (i : TspInstance) :
    metricTravelingSalespersonDec (bitEncode i) = true ↔ WellFormed i ∧ Tsp.TspFeasible i := by
  simp [metricTravelingSalespersonDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := TspInstance) bits = none) :
    metricTravelingSalespersonDec bits = false := by
  simp [metricTravelingSalespersonDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : metricTravelingSalespersonDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : TspInstance)
    (h : ¬ WellFormed i) :
    metricTravelingSalespersonDec (bitEncode i) = false := by
  simp [metricTravelingSalespersonDec, bitDecode_bitEncode, h]

/-- Three cities with a 3, 1, 1 triangle violate the triangle inequality. -/
example :
    metricTravelingSalespersonDec
      (bitEncode ((3, [[0, 3, 1], [3, 0, 1], [1, 1, 0]], 5) : TspInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact (by decide : ¬ (3 : Nat) ≤ 2)
    (h.2.2.1 0 (by decide) 2 (by decide) 1 (by decide))

/-- Traversing the edge in each direction gives a two-city tour of total length two. -/
example : metricTravelingSalespersonDec (bitEncode ((2, [[0, 1], [1, 0]], 2) : TspInstance)) =
    true := by
  let i : TspInstance := (2, [[0, 1], [1, 0]], 2)
  have hw : WellFormed i := by
    unfold WellFormed Tsp.WellFormed
    decide
  have hf : Tsp.TspFeasible i := by
    refine ⟨[0, 1], ?_, ?_, ?_, ?_⟩ <;> decide
  change metricTravelingSalespersonDec (bitEncode i) = true
  simp [metricTravelingSalespersonDec, hw, hf]

end MetaMathlibExt.Complexity.NPComplete.MetricTravelingSalesperson
