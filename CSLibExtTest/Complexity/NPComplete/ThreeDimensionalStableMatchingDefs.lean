/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ThreeDimensionalStableMatchingDefs
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalStableMatching

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ThreeDimensionalStableMatchingInstance) :
    threeDimensionalStableMatchingDec (bitEncode i) = true ↔
      WellFormed i ∧ ThreeDimensionalStableMatchingFeasible i := by
  simp [threeDimensionalStableMatchingDec, bitDecode_bitEncode]

/-- The only bijections of a two-element set are the identity and the swap. -/
private theorem fin_two_equiv (e : Fin 2 ≃ Fin 2) : e = Equiv.refl _ ∨ e = Equiv.swap 0 1 := by
  have hne : (e 0 : ℕ) ≠ e 1 := fun h => absurd (e.injective (Fin.ext h)) (by decide)
  have h₀ := (e 0).isLt
  have h₁ := (e 1).isLt
  by_cases h : (e 0 : ℕ) = 0
  · left
    ext x
    fin_cases x <;> simp <;> omega
  · right
    ext x
    fin_cases x <;> simp <;> omega

/-- A lone continuation bit is a truncated instance encoding. -/
example : threeDimensionalStableMatchingDec [true] = false := by
  have h : bitDecode (α := ThreeDimensionalStableMatchingInstance) [true] = none := rfl
  simp [threeDimensionalStableMatchingDec, h]

/-- With two agents of each kind, the families `(0, 1, 1)` and `(1, 0, 0)` leave no unstable
triple. -/
example :
    threeDimensionalStableMatchingDec
      (bitEncode ((2,
        [[(1, 1), (0, 0), (0, 1), (1, 0)], [(1, 1), (0, 0), (0, 1), (1, 0)]],
        [[(1, 0), (0, 0), (0, 1), (1, 1)], [(0, 0), (0, 1), (1, 1), (1, 0)]],
        [[(0, 1), (0, 0), (1, 1), (1, 0)], [(0, 0), (0, 1), (1, 1), (1, 0)]]) :
        ThreeDimensionalStableMatchingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed IsRanking; decide, Equiv.swap 0 1, Equiv.swap 0 1, ?_⟩
  unfold IsUnstableTriple Prefers
  decide

/-- Each of the four marriages of this instance has an unstable triple. -/
example :
    threeDimensionalStableMatchingDec
      (bitEncode ((2,
        [[(1, 1), (0, 0), (0, 1), (1, 0)], [(1, 0), (0, 1), (0, 0), (1, 1)]],
        [[(1, 1), (0, 0), (1, 0), (0, 1)], [(1, 0), (0, 1), (1, 1), (0, 0)]],
        [[(0, 0), (1, 1), (1, 0), (0, 1)], [(0, 1), (1, 0), (0, 0), (1, 1)]]) :
        ThreeDimensionalStableMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨μ, ν, hμν⟩ := ((accepts_encoding _).1 h).2
  revert hμν
  rcases fin_two_equiv μ with rfl | rfl <;> rcases fin_two_equiv ν with rfl | rfl <;>
  · unfold IsUnstableTriple Prefers
    decide

/-- A woman's preference list missing the pair `(1, 1)` is not a ranking. -/
example :
    threeDimensionalStableMatchingDec
      (bitEncode ((2,
        [[(0, 0), (0, 1), (1, 0)], [(0, 0), (0, 1), (1, 0), (1, 1)]],
        [[(0, 0), (0, 1), (1, 0), (1, 1)], [(0, 0), (0, 1), (1, 0), (1, 1)]],
        [[(0, 0), (0, 1), (1, 0), (1, 1)], [(0, 0), (0, 1), (1, 0), (1, 1)]]) :
        ThreeDimensionalStableMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2.2.2.1
  revert hw
  unfold IsRanking
  decide

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalStableMatching
