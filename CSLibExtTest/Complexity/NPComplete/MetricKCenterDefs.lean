/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MetricKCenterDefs

namespace MetaMathlibExt.Complexity.NPComplete.MetricKCenter

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open KCenter (KCenterInstance KCenterFeasible)

private theorem accepts_encoding (i : KCenterInstance) :
    metricKCenterDec (bitEncode i) = true ↔ WellFormed i ∧ KCenterFeasible i := by
  simp [metricKCenterDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := KCenterInstance) bits = none) :
    metricKCenterDec bits = false := by
  simp [metricKCenterDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : metricKCenterDec [true] = false :=
  rejects_undecodable [true] rfl

/-- On the path metric `0 - 1 - 2`, the middle vertex is a center of radius `1`. -/
example :
    metricKCenterDec (bitEncode
      (([[0, 1, 2], [1, 0, 1], [2, 1, 0]], 1, 1) : KCenterInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed KCenter.WellFormed distance; decide, [1], by decide, by decide,
    by decide, [1, 1, 1], rfl, by decide⟩

/-- Two points at distance `2` need two centers of radius `1`. -/
example :
    metricKCenterDec (bitEncode (([[0, 2], [2, 0]], 1, 1) : KCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, fs, -, hlen, hlt, assign, -, hassign⟩
  obtain ⟨h0m, h0c⟩ := hassign 0 (by decide)
  obtain ⟨h1m, h1c⟩ := hassign 1 (by decide)
  have h0lt := hlt _ h0m
  have h1lt := hlt _ h1m
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
    List.length_nil] at h0c h1c h0lt h1lt
  generalize assign.getD 0 0 = a at h0m h0c h0lt
  generalize assign.getD 1 0 = b at h1m h1c h1lt
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp at h0c h1c <;> try omega
  rcases fs with _ | ⟨x, _ | ⟨y, fs⟩⟩
  · simp at h0m
  · simp at h0m h1m; omega
  · simp at hlen

/-- A matrix violating the triangle inequality (`5 > 1 + 1`) is malformed here. -/
example :
    metricKCenterDec (bitEncode
      (([[0, 5, 1], [5, 0, 1], [1, 1, 0]], 1, 1) : KCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, -, -, htri, -⟩, -⟩
  exact absurd (htri 0 (by decide) 2 (by decide) 1 (by decide)) (by decide)

/-- The same non-metric instance is accepted by generalized nonmetric k-center. -/
example :
    KCenter.kCenterDec (bitEncode
      (([[0, 5, 1], [5, 0, 1], [1, 1, 0]], 1, 1) : KCenterInstance)) = true := by
  simp only [KCenter.kCenterDec, bitDecode_bitEncode, decide_eq_true_eq]
  exact ⟨by unfold KCenter.WellFormed; decide, [2], by decide, by decide, by decide,
    [2, 2, 2], rfl, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.MetricKCenter
