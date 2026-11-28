/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.OptimalMorseMatchingDefs

namespace MetaMathlibExt.Complexity.NPComplete.OptimalMorseMatching

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : OptimalMorseMatchingInstance) :
    optimalMorseMatchingDec (bitEncode i) = true ↔
      WellFormed i ∧ OptimalMorseMatchingFeasible i := by
  simp [optimalMorseMatchingDec, bitDecode_bitEncode]

/-- Closure under faces only needs the finitely many sublists of each face. -/
private theorem wellFormed_iff (i : OptimalMorseMatchingInstance) :
    WellFormed i ↔ (∀ F ∈ i.1, F ≠ [] ∧ F.Pairwise (· < ·)) ∧ i.1.Nodup ∧
      ∀ F ∈ i.1, ∀ G ∈ F.sublists, G ≠ [] → G ∈ i.1 := by
  simp [WellFormed, List.mem_sublists]

/-- A lone continuation bit is a truncated instance encoding. -/
example : optimalMorseMatchingDec [true] = false := by
  have h : bitDecode (α := OptimalMorseMatchingInstance) [true] = none := rfl
  simp [optimalMorseMatchingDec, h]

/-- On a single edge, pairing the vertex `0` with the edge leaves only the vertex `1`
critical. -/
example :
    optimalMorseMatchingDec
      (bitEncode (([[0], [1], [0, 1]], 1) : OptimalMorseMatchingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨(wellFormed_iff _).2 (by decide), [([0], [0, 1])], by unfold Covers; decide,
    by decide, ⟨fun F => if F = [0] then 2 else if F = [0, 1] then 1 else 0, ?_⟩, by decide⟩
  unfold Covers
  decide

/-- A single vertex has no facet pair, so it stays critical and the bound zero fails. -/
example :
    optimalMorseMatchingDec
      (bitEncode (([[0]], 0) : OptimalMorseMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨M, hM, -, -, hcrit⟩ := ((accepts_encoding _).1 h).2
  have hM0 : M = [] := by
    rcases M with _ | ⟨p, M⟩
    · rfl
    · obtain ⟨h₁, h₂, -, h₃⟩ := hM p (by simp)
      simp only [List.mem_singleton] at h₁ h₂
      rw [h₁, h₂] at h₃
      simp at h₃
  subst hM0
  simp at hcrit

/-- The edge `{0, 1}` without its vertices is not closed under faces. -/
example :
    optimalMorseMatchingDec
      (bitEncode (([[0, 1]], 0) : OptimalMorseMatchingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := (wellFormed_iff _).1 ((accepts_encoding _).1 h).1
  revert hw
  decide

end MetaMathlibExt.Complexity.NPComplete.OptimalMorseMatching
