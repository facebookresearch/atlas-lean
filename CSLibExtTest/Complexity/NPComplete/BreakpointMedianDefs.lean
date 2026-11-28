/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BreakpointMedianDefs

namespace MetaMathlibExt.Complexity.NPComplete.BreakpointMedian

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : BreakpointMedianInstance) :
    breakpointMedianDec (bitEncode i) = true ↔ WellFormed i ∧ BreakpointMedianFeasible i := by
  simp [breakpointMedianDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : breakpointMedianDec [true] = false := by
  have h : bitDecode (α := BreakpointMedianInstance) [true] = none := rfl
  simp [breakpointMedianDec, h]

/-- The signed permutations `+1 +2`, `+1 +2` and `+2 +1`. -/
private abbrev π₀ : List (ℕ × Bool) := [(1, true), (2, true)]
private abbrev π₂ : List (ℕ × Bool) := [(2, true), (1, true)]

/-- The median `+1 +2` is at distance `0`, `0` and `3` from the three permutations. -/
example : breakpointMedianDec (bitEncode ((π₀, π₀, π₂, 3) : BreakpointMedianInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed IsSignedPerm; decide, π₀,
    by unfold IsSignedPerm; decide, by decide⟩

/-- Every signed permutation on two elements has total breakpoint distance at least `3` to the
same three permutations, so the bound `2` is unattainable. -/
example : breakpointMedianDec (bitEncode ((π₀, π₀, π₂, 2) : BreakpointMedianInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, σ, hσ, hk⟩
  unfold IsSignedPerm at hσ
  have hl := hσ.length_eq
  simp only [List.length_map, List.length_cons, List.length_nil] at hl
  match σ, hl with
  | [(a, s), (b, t)], _ =>
    have ha : a ∈ List.range' 1 2 := hσ.subset (by simp)
    have hb : b ∈ List.range' 1 2 := hσ.subset (by simp)
    have key : ∀ a ∈ List.range' 1 2, ∀ b ∈ List.range' 1 2, ∀ s t : Bool,
        3 ≤ ExemplarBreakpointDistance.breakpointDistance π₀ [(a, s), (b, t)] +
          ExemplarBreakpointDistance.breakpointDistance π₀ [(a, s), (b, t)] +
          ExemplarBreakpointDistance.breakpointDistance π₂ [(a, s), (b, t)] := by
      decide
    exact absurd hk (Nat.not_le.2 (key a ha b hb s t))

end MetaMathlibExt.Complexity.NPComplete.BreakpointMedian
