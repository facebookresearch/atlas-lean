/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `f28b502e41` (PR #5951).
-/

module

public import MathlibExt.Combinatorics.Digraph.PathCover
import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathlibExtTest.Combinatorics.Digraph.PathCover

open MathlibExt.Combinatorics.Digraph.PathCoverWanted

/-- The 3-chain `0 → 1 → 2` (with the transitive `0 → 2` arc). A reducible
abbrev so `decide` can evaluate adjacency. -/
private abbrev chainDAG : Digraph (Fin 3) := ⟨fun x y => x.val < y.val⟩

private theorem chainDAG_trans : IsTransitiveDAG chainDAG :=
  ⟨by decide, by decide⟩

/-- The full vertex set of the 3-chain is a directed path. -/
private theorem chainDAG_full_isPath : IsPath chainDAG {0, 1, 2} := by
  refine ⟨[0, 1, 2], by decide, by decide, by decide, ?_⟩
  ext a
  simp

-- Path/chain round-trip on the 3-chain.
example : IsPath chainDAG {0, 1, 2} :=
  isPath_of_isChain chainDAG chainDAG_trans ⟨0, by decide⟩
    (isChain_of_isPath chainDAG chainDAG_trans chainDAG_full_isPath)

-- A singleton is a chain, hence a path.
example : IsPath chainDAG {1} := by
  apply isPath_of_isChain chainDAG chainDAG_trans ⟨1, by decide⟩
  rw [Finset.coe_singleton]
  exact IsChain.singleton

-- The order API computes reachability without unfolding.
example : (toPartialOrder chainDAG chainDAG_trans).le 0 2 := by
  rw [toPartialOrder_le]
  exact Or.inr (by decide)

/-- The singleton family `{{0, 1, 2}}` covers the 3-chain with one path. -/
private theorem chainDAG_cover : IsPathCover chainDAG {{0, 1, 2}} := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact ⟨chainDAG_full_isPath, ⟨0, by decide⟩⟩
  · intro s hs t ht hne
    rw [Finset.mem_singleton] at hs ht
    subst hs; subst ht
    exact absurd rfl hne
  · intro a
    refine ⟨{0, 1, 2}, Finset.mem_singleton_self _, ?_⟩
    fin_cases a <;> decide

-- One path suffices for the 3-chain.
example : minPathCoverSize chainDAG ≤ 1 := by
  have h := minPathCoverSize_le_card chainDAG chainDAG_cover
  have hcard : (({{0, 1, 2}} : Finset (Finset (Fin 3)))).card = 1 := by decide
  omega

-- The 3-chain needs exactly one path: every cover is nonempty.
example : minPathCoverSize chainDAG = 1 := by
  refine le_antisymm ?_ ?_
  · have h := minPathCoverSize_le_card chainDAG chainDAG_cover
    have hcard : (({{0, 1, 2}} : Finset (Finset (Fin 3)))).card = 1 := by decide
    omega
  · obtain ⟨P, hP, hcard⟩ :=
      exists_isPathCover_card_eq_minPathCoverSize chainDAG
    obtain ⟨s, hs, -⟩ := hP.2.2 (0 : Fin 3)
    have hpos : 1 ≤ P.card := Finset.card_pos.mpr ⟨s, hs⟩
    omega

/-- Two isolated vertices: no arcs at all. -/
private abbrev discreteDAG : Digraph (Fin 2) := ⟨fun _ _ => False⟩

private theorem discreteDAG_trans : IsTransitiveDAG discreteDAG :=
  ⟨by decide, by decide⟩

/-- Singleton paths cover the two isolated vertices. -/
private theorem discreteDAG_cover : IsPathCover discreteDAG {{0}, {1}} := by
  have h0 : IsPath discreteDAG ({0} : Finset (Fin 2)) := by
    refine ⟨[0], by decide, by decide, by decide, ?_⟩
    ext a
    simp
  have h1 : IsPath discreteDAG ({1} : Finset (Fin 2)) := by
    refine ⟨[1], by decide, by decide, by decide, ?_⟩
    ext a
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨h0, ⟨0, by decide⟩⟩
    · exact ⟨h1, ⟨1, by decide⟩⟩
  · intro s hs t ht hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  · intro a
    fin_cases a
    · exact ⟨{0}, by simp, by decide⟩
    · exact ⟨{1}, by simp, by decide⟩

-- Two isolated vertices need two paths: `{0, 1}` is an antichain.
example : minPathCoverSize discreteDAG = 2 := by
  have hub : minPathCoverSize discreteDAG ≤ 2 := by
    have h := minPathCoverSize_le_card discreteDAG discreteDAG_cover
    have hcard : (({{0}, {1}} : Finset (Finset (Fin 2)))).card = 2 := by decide
    omega
  have hlb : 2 ≤ minPathCoverSize discreteDAG := by
    rw [minPathCover_eq_maxAntichain discreteDAG discreteDAG_trans]
    have hanti : @IsAntichain (Fin 2)
        (toPartialOrder discreteDAG discreteDAG_trans).le
        ↑(({0, 1} : Finset (Fin 2))) := by
      intro x hx y hy hne hle
      rw [Finset.coe_insert, Finset.coe_singleton] at hx hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rw [toPartialOrder_le] at hle
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hne
      · rcases hle with h | h
        · exact absurd h (by decide)
        · exact h
      · rcases hle with h | h
        · exact absurd h (by decide)
        · exact h
      · exact absurd rfl hne
    have h2 := @MathlibExt.Combinatorics.Order.DilworthWanted.card_le_maxAntichainSize
      (Fin 2) inferInstance (toPartialOrder discreteDAG discreteDAG_trans)
      ({0, 1} : Finset (Fin 2)) hanti
    have hcard : (({0, 1} : Finset (Fin 2))).card = 2 := by decide
    show 2 ≤ @MathlibExt.Combinatorics.Order.DilworthWanted.maxAntichainSize (Fin 2)
      inferInstance (toPartialOrder discreteDAG discreteDAG_trans)
    omega
  omega

end MathlibExtTest.Combinatorics.Digraph.PathCover
