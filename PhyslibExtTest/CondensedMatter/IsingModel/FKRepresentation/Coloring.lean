/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Coloring

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Coloring`

On the single edge `⊤ : SimpleGraph (Fin 2)`:
* `Compatible` (decided): with the edge open only constant colorings are compatible, with the edge
  closed every coloring is;
* `card_compatible` with the edge open: there are exactly `3 = 3^1` compatible `3`-colorings;
* `esJointProb` vanishes on an incompatible pair (`esJointProb_incompatible`) and equals
  `p / Z_FK` on a compatible pair with the edge open (`esJointProb_eq`).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.Coloring

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.IsingFK

/-- The bond configuration with every edge open. -/
def allOpen : ConfigSpace (Sym2 (Fin 2)) := fun _ => true

/-- The bond configuration with every edge closed. -/
def allClosed : ConfigSpace (Sym2 (Fin 2)) := fun _ => false

-- With the edge open, a non-constant coloring is not compatible.
example : ¬ Compatible (⊤ : SimpleGraph (Fin 2)) (![0, 1] : Fin 2 → Fin 2) allOpen := by
  decide

-- With the edge open, a constant coloring is compatible.
example : Compatible (⊤ : SimpleGraph (Fin 2)) (![1, 1] : Fin 2 → Fin 2) allOpen := by
  decide

-- With the edge closed, every coloring is compatible.
example : Compatible (⊤ : SimpleGraph (Fin 2)) (![0, 1] : Fin 2 → Fin 2) allClosed := by
  decide

/-- With the edge open there is a single open cluster. -/
lemma numClusters_allOpen : numClusters (⊤ : SimpleGraph (Fin 2)) allOpen = 1 := by
  unfold numClusters
  rw [Fintype.card_eq_one_iff]
  refine ⟨(openSub (⊤ : SimpleGraph (Fin 2)) allOpen).connectedComponentMk 0, fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    rw [SimpleGraph.ConnectedComponent.eq]
    fin_cases v
    · rfl
    · exact SimpleGraph.Adj.reachable ⟨by simp, rfl⟩

-- With the edge open there are exactly three compatible `3`-colorings.
example : Nat.card {σ : Fin 2 → Fin 3 // Compatible (⊤ : SimpleGraph (Fin 2)) σ allOpen} = 3 := by
  rw [card_compatible, numClusters_allOpen, pow_one]

-- An incompatible pair has joint probability zero.
example (p : ℝ) :
    esJointProb (⊤ : SimpleGraph (Fin 2)) 2 p (![0, 1] : Fin 2 → Fin 2) allOpen = 0 :=
  esJointProb_incompatible _ p _ _ (by decide)

-- A compatible pair has joint probability `p^o (1-p)^c / Z_FK`.
example (p : ℝ) :
    esJointProb (⊤ : SimpleGraph (Fin 2)) 2 p (![1, 1] : Fin 2 → Fin 2) allOpen =
      (p ^ openCount (⊤ : SimpleGraph (Fin 2)) allOpen *
          (1 - p) ^ closedCount (⊤ : SimpleGraph (Fin 2)) allOpen) /
        fkZ (⊤ : SimpleGraph (Fin 2)) p 2 := by
  rw [esJointProb_eq]
  split_ifs with h
  · rfl
  · exact absurd (by decide) h

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.Coloring
