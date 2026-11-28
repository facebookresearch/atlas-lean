/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetCoverDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetCover

/-- Three subsets of the universe `{0, 1, 2}` with the bound `K`. -/
private abbrev chain (K : ℕ) : SetCoverInstance :=
  (3, [[0, 1], [1, 2], [2]], K)

/-- The chain instance is well formed. -/
private theorem chain_wellFormed (K : ℕ) : WellFormed (chain K) := by
  have h : ∀ s ∈ ([[0, 1], [1, 2], [2]] : List (List ℕ)), s.Nodup ∧ ∀ x ∈ s, x < 3 := by decide
  exact h

/-- The first and last subsets, a sublist of the subsets, cover the universe within the bound
`2`. -/
private theorem chain_two_feasible : SetCoverFeasible (chain 2) :=
  ⟨[[0, 1], [2]], by decide, by decide, by decide⟩

/-- No single subset contains both `0` and `2`, so the bound `1` cannot be met. -/
private theorem chain_one_infeasible : ¬ SetCoverFeasible (chain 1) := by
  rintro ⟨sub, hsub, hlen, hcov⟩
  rcases sub with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · obtain ⟨s, hs, -⟩ := hcov 0 (by decide)
    simp at hs
  · have hs : s ∈ [[0, 1], [1, 2], [2]] := hsub.subset (by simp)
    have h0 := hcov 0 (by decide)
    have h2 := hcov 2 (by decide)
    simp only [List.mem_singleton, exists_eq_left] at h0 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp at h0 h2
  · simp at hlen

/-- The bound counts chosen subsets, not covered elements: `[1, 2]` alone does not cover `0`. -/
example : ¬ SetCoverFeasible ((3, [[1, 2]], 5) : SetCoverInstance) := by
  rintro ⟨sub, hsub, -, hcov⟩
  obtain ⟨s, hs, h0⟩ := hcov 0 (by decide)
  have : s ∈ [[1, 2]] := hsub.subset hs
  simp only [List.mem_singleton] at this
  subst this
  simp at h0

/-- An empty universe is covered by no subsets, with the bound `0`. -/
private theorem empty_feasible : SetCoverFeasible ((0, [], 0) : SetCoverInstance) :=
  ⟨[], by decide, by decide, by decide⟩

/-- A non-empty universe with no subsets is not covered, whatever the bound. -/
example : ¬ SetCoverFeasible ((1, [], 4) : SetCoverInstance) := by
  rintro ⟨sub, hsub, -, hcov⟩
  obtain ⟨s, hs, -⟩ := hcov 0 (by decide)
  simp [List.sublist_nil.mp hsub] at hs

/-- A subset with a repeated entry is malformed, although it covers the universe. -/
private theorem repeated_feasible : SetCoverFeasible ((1, [[0, 0]], 1) : SetCoverInstance) :=
  ⟨[[0, 0]], by decide, by decide, by decide⟩

private theorem repeated_malformed : ¬ WellFormed ((1, [[0, 0]], 1) : SetCoverInstance) := by
  unfold WellFormed; decide

/-- A subset with an entry outside the universe is malformed, although it covers the universe. -/
private theorem outOfRange_feasible : SetCoverFeasible ((1, [[0, 1]], 1) : SetCoverInstance) :=
  ⟨[[0, 1]], by decide, by decide, by decide⟩

private theorem outOfRange_malformed : ¬ WellFormed ((1, [[0, 1]], 1) : SetCoverInstance) := by
  unfold WellFormed; decide

/-- The empty subset is allowed. -/
example : WellFormed ((2, [[], [0, 1]], 1) : SetCoverInstance) := by
  unfold WellFormed; decide

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the chain instance with the bound `2`. -/
example : setCoverDec (bitEncode (chain 2)) = true := by
  simp [setCoverDec, chain_wellFormed, chain_two_feasible]

/-- It rejects the well-formed chain instance with the bound `1`. -/
example : setCoverDec (bitEncode (chain 1)) = false := by
  simp [setCoverDec, chain_one_infeasible]

/-- It accepts the empty universe with the bound `0`. -/
example : setCoverDec (bitEncode ((0, [], 0) : SetCoverInstance)) = true := by
  have hw : WellFormed ((0, [], 0) : SetCoverInstance) := by unfold WellFormed; decide
  simp [setCoverDec, hw, empty_feasible]

/-- It rejects malformed instances even though they are feasible. -/
example :
    setCoverDec (bitEncode ((1, [[0, 0]], 1) : SetCoverInstance)) = false ∧
      setCoverDec (bitEncode ((1, [[0, 1]], 1) : SetCoverInstance)) = false := by
  simp [setCoverDec, repeated_malformed, outOfRange_malformed]

example :
    SetCoverFeasible ((1, [[0, 0]], 1) : SetCoverInstance) ∧
      SetCoverFeasible ((1, [[0, 1]], 1) : SetCoverInstance) :=
  ⟨repeated_feasible, outOfRange_feasible⟩

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : setCoverDec [] = false := by
  have h : bitDecode (α := SetCoverInstance) [] = none := rfl
  simp [setCoverDec, h]

end MetaMathlibExt.Complexity.NPComplete.SetCover
