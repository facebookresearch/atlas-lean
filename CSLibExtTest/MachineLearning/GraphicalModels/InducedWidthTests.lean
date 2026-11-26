/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GraphicalModels.InducedWidth
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for induced width -/

namespace CSLibExtTest.MachineLearning.GraphicalModels

open Cslib.MachineLearning.GraphicalModels

-- The path with centre 2. Filling at 2 must connect 0 and 1.
private def twoLeafPath : SimpleGraph (Fin 3) where
  Adj x y := (x = 2 ∧ y ≠ 2) ∨ (y = 2 ∧ x ≠ 2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.2 h.1) (fun h => h.2 h.1)⟩

example : ¬ twoLeafPath.Adj 0 1 ∧
    (inducedGraph (Equiv.refl (Fin 3)) twoLeafPath).Adj 0 1 := by
  have hr : (List.finRange 3).reverse = [2, 1, 0] := by decide
  constructor
  · norm_num [twoLeafPath]
  · simp [inducedGraph, hr, fillEarlierNeighbours_adj, twoLeafPath]

example : inducedWidth (Equiv.refl (Fin 3)) twoLeafPath = 2 := by
  classical
  let order := Equiv.refl (Fin 3)
  let G := inducedGraph order twoLeafPath
  let earlier (v : Fin 3) := Finset.univ.filter fun u => order u < order v ∧ G.Adj v u
  change Finset.univ.sup (fun v => (earlier v).card) = 2
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    have hsub : earlier v ⊆ Finset.univ.erase v := by
      intro u hu
      have hlt := (Finset.mem_filter.mp hu).2.1
      exact Finset.mem_erase.mpr ⟨fun he => (lt_irrefl (order v)) (he ▸ hlt), Finset.mem_univ _⟩
    calc
      (earlier v).card ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
      _ = 2 := by rw [Finset.card_erase_of_mem (Finset.mem_univ v)]; decide
  · have hle := le_inducedGraph order twoLeafPath
    have hsub : ({0, 1} : Finset (Fin 3)) ⊆ earlier 2 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · subst u
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, hle (by norm_num [twoLeafPath])⟩
      · have h' := Finset.mem_singleton.mp h
        subst u
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, hle (by norm_num [twoLeafPath])⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair (by decide : (0 : Fin 3) ≠ 1)] at hcard
    exact hcard.trans (Finset.le_sup (f := fun v => (earlier v).card) (Finset.mem_univ _))

-- Here eliminating 3 first creates 0–2. Eliminating 2 then uses that new edge to add 0–1.
private def fourVertexPath : SimpleGraph (Fin 4) where
  Adj x y := (x = 0 ∧ y = 3) ∨ (x = 3 ∧ y = 0) ∨
    (x = 3 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2)
  symm := ⟨by intro x y h; aesop⟩
  loopless := ⟨by intro x h; fin_cases x <;> simp_all⟩

example : ¬ fourVertexPath.Adj 0 1 ∧
    (inducedGraph (Equiv.refl (Fin 4)) fourVertexPath).Adj 0 1 := by
  have hr : (List.finRange 4).reverse = [3, 2, 1, 0] := by decide
  constructor
  · norm_num [fourVertexPath]
  · simp [inducedGraph, hr, fillEarlierNeighbours_adj, fourVertexPath]

-- Ordinary width is two in this order. Filling at 4 adds 0–3, so vertex 3
-- has three earlier neighbours in the induced graph.
private def forkGraph : SimpleGraph (Fin 5) where
  Adj x y := (x = 3 ∧ (y = 1 ∨ y = 2 ∨ y = 4)) ∨ (y = 3 ∧ (x = 1 ∨ x = 2 ∨ x = 4)) ∨
    (x = 4 ∧ y = 0) ∨ (y = 4 ∧ x = 0)
  symm := ⟨by intro x y h; aesop⟩
  loopless := ⟨by intro x h; fin_cases x <;> simp_all⟩

example : 3 ≤ inducedWidth (Equiv.refl (Fin 5)) forkGraph := by
  classical
  let order := Equiv.refl (Fin 5)
  let earlier (v : Fin 5) :=
    Finset.univ.filter fun u => order u < order v ∧ (inducedGraph order forkGraph).Adj v u
  change 3 ≤ Finset.univ.sup fun v => (earlier v).card
  have hr : (List.finRange 5).reverse = [4, 3, 2, 1, 0] := by decide
  have h0 : (inducedGraph order forkGraph).Adj 3 0 := by
    simp [order, inducedGraph, hr, fillEarlierNeighbours_adj, forkGraph]
  have hle := le_inducedGraph order forkGraph
  have h1 : (inducedGraph order forkGraph).Adj 3 1 := hle (by norm_num [forkGraph])
  have h2 : (inducedGraph order forkGraph).Adj 3 2 := hle (by norm_num [forkGraph])
  have hsub : ({0, 1, 2} : Finset (Fin 5)) ⊆ earlier 3 := by
    intro u hu
    have hm : u = 0 ∨ u = 1 ∨ u = 2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hu
    rcases hm with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, h0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, h1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, h2⟩
  have hcard : ({0, 1, 2} : Finset (Fin 5)).card = 3 := by decide
  rw [← hcard]
  exact (Finset.card_le_card hsub).trans (Finset.le_sup (f := fun v => (earlier v).card)
    (Finset.mem_univ (3 : Fin 5)))

example : inducedWidth (Equiv.refl (Fin 0)) (⊥ : SimpleGraph (Fin 0)) = 0 := by
  simp [inducedWidth]

end CSLibExtTest.MachineLearning.GraphicalModels
