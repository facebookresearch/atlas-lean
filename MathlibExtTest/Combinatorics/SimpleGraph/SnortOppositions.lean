/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.Hasse
import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions

open MetaMathlibExt SimpleGraph

-- On the empty vertex type the identity gives the empty matching.
example (G : SimpleGraph Empty) : ∃ M : Gᶜ.Subgraph, IsOppositionMatching Gᶜ M :=
  (isOpposable_iff_exists_oppositionMatching G).mp ⟨.refl, fun v => nomatch v⟩

-- A single edge in the complement gives an opposition on two isolated vertices.
example : IsOpposable (⊥ : SimpleGraph Bool) := by
  rw [isOpposable_iff_exists_oppositionMatching, compl_bot]
  refine ⟨⊤, Subgraph.isPerfectMatching_iff.mpr ?_, ?_⟩
  · change ∀ v : Bool, ∃! w, v ≠ w
    exact fun v => ⟨!v, Bool.self_ne_not v, fun _ h => Bool.eq_not_iff.mpr h.symm⟩
  · change ∀ a b c d : Bool, a ≠ b → c ≠ d → s(a, b) ≠ s(c, d) →
      (a ≠ c ↔ b ≠ d) ∧ (a ≠ d ↔ b ≠ c)
    decide

-- The end edges of the four-vertex path are forced, but only their inner ends are adjacent.
example (M : (pathGraph 4).Subgraph) : ¬ IsOppositionMatching (pathGraph 4) M := by
  rintro ⟨hperfect, hpairs⟩
  obtain ⟨a, ha⟩ := (Subgraph.isPerfectMatching_iff.mp hperfect 0).exists
  obtain ⟨b, hb⟩ := (Subgraph.isPerfectMatching_iff.mp hperfect 3).exists
  have left : ∀ v, (pathGraph 4).Adj 0 v → v = 1 := by decide
  have right : ∀ v, (pathGraph 4).Adj 3 v → v = 2 := by decide
  obtain rfl := left a (M.adj_sub ha)
  obtain rfl := right b (M.adj_sub hb)
  have h := (hpairs 0 1 3 2 ha hb (by decide)).1
  exact (by decide : ¬ (pathGraph 4).Adj 0 3) (h.mpr (by decide))

private abbrev pathSquare := strongProd (pathGraph 3) (pathGraph 3)

-- Strong-product edges can change either coordinate or both; they are not loops.
example : pathSquare.Adj (0, 0) (1, 0) := by
  rw [pathSquare, MetaMathlibExt.strongProd_adj]
  decide

example : pathSquare.Adj (0, 0) (0, 1) := by
  rw [pathSquare, MetaMathlibExt.strongProd_adj]
  decide

example : pathSquare.Adj (0, 0) (1, 1) := by
  rw [pathSquare, MetaMathlibExt.strongProd_adj]
  decide

example : ¬ pathSquare.Adj (0, 0) (0, 0) := by
  rw [pathSquare, MetaMathlibExt.strongProd_adj]
  decide

example : ¬ pathSquare.Adj (0, 0) (1, 2) := by
  rw [pathSquare, MetaMathlibExt.strongProd_adj]
  decide

-- The residual graph is empty and the one vertex of H is universal vacuously.
example : IsAlmostOpposable (strongProd (⊥ : SimpleGraph Unit) (⊥ : SimpleGraph Unit)) := by
  apply isAlmostOpposable_strongProd
  · refine ⟨(), Set.univ, Set.mem_univ _, ?_, .refl, ?_⟩
    · intro x _
      exact Set.mem_insert_iff.mpr (Or.inl (Subsingleton.elim _ _))
    · intro x
      exact False.elim (x.2 (Set.mem_univ _))
  · exact ⟨(), fun w hw => (hw (Subsingleton.elim _ _)).elim⟩

-- Two isolated vertices survive deletion and are swapped; H is a noncomplete path.
example : IsAlmostOpposable (strongProd (⊥ : SimpleGraph (Fin 3)) (pathGraph 3)) := by
  apply isAlmostOpposable_strongProd
  · let S : Set (Fin 3) := {0}
    refine ⟨0, S, rfl, ?_, ?_⟩
    · exact fun _ hx => Set.mem_insert_iff.mpr (Or.inl hx)
    let flip (x : ↥Sᶜ) : ↥Sᶜ :=
      ⟨if x.val = 1 then 2 else 1, by
        change (if x.val = 1 then (2 : Fin 3) else 1) ≠ 0
        split <;> decide⟩
    have hcases (x : ↥Sᶜ) : x.val = 1 ∨ x.val = 2 := by
      have hx : x.val ≠ 0 := x.property
      omega
    have hinv : Function.Involutive flip := by
      intro x
      apply Subtype.ext
      rcases hcases x with hx | hx <;> simp [flip, hx]
    refine ⟨⟨hinv.toPerm flip, Iff.rfl⟩, fun x => ⟨hinv x, ?_, id⟩⟩
    intro heq
    have hval : (flip x).val = x.val := congrArg Subtype.val heq
    rcases hcases x with hx | hx <;> simp [flip, hx] at hval
  · exact ⟨1, by decide⟩
