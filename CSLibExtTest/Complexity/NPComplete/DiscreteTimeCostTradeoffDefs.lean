/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DiscreteTimeCostTradeoffDefs

namespace MetaMathlibExt.Complexity.NPComplete.DiscreteTimeCostTradeoff

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : DiscreteTimeCostTradeoffInstance) :
    discreteTimeCostTradeoffDec (bitEncode i) = true ↔
      WellFormed i ∧ DiscreteTimeCostTradeoffFeasible i := by
  simp [discreteTimeCostTradeoffDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : discreteTimeCostTradeoffDec [true] = false := by
  have h : bitDecode (α := DiscreteTimeCostTradeoffInstance) [true] = none := rfl
  simp [discreteTimeCostTradeoffDec, h]

/-- Two activities, the first preceding the second, with alternatives `(time, cost)`
`(1, 5), (2, 3)` and `(1, 4), (3, 1)`, due date `3` and budget `b`. -/
private abbrev chain (b : ℕ) : DiscreteTimeCostTradeoffInstance :=
  (2, [(0, 1)], [[(1, 5), (2, 3)], [(1, 4), (3, 1)]], 3, b)

/-- Budget `8`: the slower first alternative and the faster second one finish at time `3` for
cost `3 + 4 = 7`. -/
example : discreteTimeCostTradeoffDec (bitEncode (chain 8)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    fun v => if v = 0 then 1 else 0, ?_, ⟨fun v => if v = 0 then 0 else 2, ?_, ?_⟩, ?_⟩
  · intro v (hv : v < 2)
    obtain rfl | rfl : v = 0 ∨ v = 1 := by omega
    all_goals decide
  · intro a ha
    obtain rfl := List.mem_singleton.1 ha
    decide
  · intro v (hv : v < 2)
    obtain rfl | rfl : v = 0 ∨ v = 1 := by omega
    all_goals decide
  · decide

/-- Budget `6`: meeting the due date needs the faster second alternative (cost `4`), and then
the first activity costs at least `3`, so every realization exceeds the budget or the due date. -/
example : discreteTimeCostTradeoffDec (bitEncode (chain 6)) = false := by
  cases h : discreteTimeCostTradeoffDec (bitEncode (chain 6)) with
  | false => rfl
  | true =>
    obtain ⟨-, σ, hσ, ⟨S, harc, hdue⟩, hcost⟩ := (accepts_encoding _).1 h
    have h₀ := hσ 0 (by decide)
    have h₁ := hσ 1 (by decide)
    have ha := harc (0, 1) (List.mem_singleton_self _)
    have hd := hdue 1 (by decide)
    simp only [alternatives, time, cost, Finset.sum_range_succ, Finset.sum_range_zero] at *
    simp at h₀ h₁
    obtain e₀ | e₀ : σ 0 = 0 ∨ σ 0 = 1 := by omega
    all_goals obtain e₁ | e₁ : σ 1 = 0 ∨ σ 1 = 1 := by omega
    all_goals simp [e₀, e₁] at ha hd hcost
    all_goals omega

end MetaMathlibExt.Complexity.NPComplete.DiscreteTimeCostTradeoff
