/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DeliveryVanRoutingDefs

namespace MetaMathlibExt.Complexity.NPComplete.DeliveryVanRouting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : DeliveryVanRoutingInstance) :
    deliveryVanRoutingDec (bitEncode i) = true ↔ WellFormed i ∧ DeliveryVanRoutingFeasible i := by
  simp [deliveryVanRoutingDec, bitDecode_bitEncode]

/-- Two vertices joined by the arc `0 → 1` of weight `-1` and the arc `1 → 0` of weight `1`,
with start vertex `s`. -/
private abbrev twoCycle (s : ℕ) : DeliveryVanRoutingInstance :=
  (2, [(0, 1, (0, 1)), (1, 0, (1, 0))], s)

/-- The two-cycle with an extra loop `0 → 0` of weight `0`, starting at `0`. -/
private abbrev loopCycle : DeliveryVanRoutingInstance :=
  (2, [(0, 0, (0, 0)), (0, 1, (0, 1)), (1, 0, (1, 0))], 0)

example : WellFormed (twoCycle 0) := by unfold WellFormed; decide

example : WellFormed (twoCycle 1) := by unfold WellFormed; decide

/-- Starting at `0`, the tour `0 → 1 → 0` has prefix weights `0, -1, 0`. -/
private theorem twoCycle_zero_feasible : DeliveryVanRoutingFeasible (twoCycle 0) := by
  refine ⟨[⟨0, by decide⟩, ⟨1, by decide⟩], by decide, ?_, ⟨by decide, by decide, by decide⟩,
    by decide⟩
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  obtain rfl : j = 0 := by omega
  decide +revert

/-- Yes-instance: the van leaves `0`, gains one unit of slack, and returns. -/
example : deliveryVanRoutingDec (bitEncode (twoCycle 0)) = true :=
  (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, twoCycle_zero_feasible⟩

/-- The only arc leaving `1` has positive weight. -/
private theorem twoCycle_one_key : ∀ a : Fin (twoCycle 1).2.1.length,
    ((twoCycle 1).2.1[a]).1 = 1 → 0 < weight (twoCycle 1).2.1[a] := by
  decide

/-- Starting at `1`, the only arc leaving the start has weight `1`, so the first prefix is
positive. -/
private theorem twoCycle_one_not_feasible : ¬ DeliveryVanRoutingFeasible (twoCycle 1) := by
  rintro ⟨P, -, -, ⟨h0, hs, -⟩, hpre⟩
  cases P with
  | nil => simp at h0
  | cons a l =>
    have h1 : weight (twoCycle 1).2.1[a] ≤ 0 := by
      simpa using hpre 1 (by simp)
    exact absurd (twoCycle_one_key a hs) (not_lt.2 h1)

/-- No-instance: the same well-formed graph started at `1` has no feasible tour. -/
example : deliveryVanRoutingDec (bitEncode (twoCycle 1)) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => twoCycle_one_not_feasible ((dec_bitEncode _).1 h).2

/-- The loop is harmless for feasibility: the tour loop, `0 → 1`, `1 → 0` has prefix weights
`0, 0, -1, 0`. -/
example : DeliveryVanRoutingFeasible loopCycle := by
  refine ⟨[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], by decide, ?_,
    ⟨by decide, by decide, by decide⟩, by decide⟩
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide +revert

/-- Malformed: a loop arc is rejected, although the instance has a feasible tour. -/
example : deliveryVanRoutingDec (bitEncode loopCycle) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := DeliveryVanRoutingInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : deliveryVanRoutingDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.DeliveryVanRouting
