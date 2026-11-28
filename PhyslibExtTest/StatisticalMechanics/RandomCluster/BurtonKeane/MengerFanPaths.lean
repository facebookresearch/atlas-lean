/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerFanPaths

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerFanPaths`

* `bc19_menger_minmax` on the complete graph on `Fin 3` with both sides the whole vertex set: every
  separator has three vertices, so three disjoint paths exist (instance).
* `bc19_hardDir_all` applied to the path graph `pathGraph 4` with `k = 4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerFanPaths

open _root_.StatMech.Walls

/-- With both sides the whole vertex set, every separator is the whole vertex set: each trivial
walk must be hit. -/
theorem sep_univ {V : Type} {G : SimpleGraph V} {C : Set V}
    (hC : bc16_IsSeparator G Set.univ Set.univ C) : C = Set.univ :=
  Set.eq_univ_of_forall fun s => by
    obtain ⟨c, hc, hcs⟩ := hC (Set.mem_univ s) (Set.mem_univ s) SimpleGraph.Walk.nil
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hcs
    exact hcs ▸ hc

/-- Every separator between `univ` and `univ` in a graph on `Fin n` has `n` vertices. -/
theorem sep_card {n : ℕ} {G : SimpleGraph (Fin n)} (C : Set (Fin n))
    (hC : bc16_IsSeparator G Set.univ Set.univ C) : n ≤ C.ncard := by
  rw [sep_univ hC, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

-- Menger's theorem on the triangle.
example : ∃ _F : bc16_DisjointPathFamily (⊤ : SimpleGraph (Fin 3)) Set.univ Set.univ (Fin 3),
    ∀ C, bc16_IsSeparator (⊤ : SimpleGraph (Fin 3)) Set.univ Set.univ C →
      Fintype.card (Fin 3) ≤ C.ncard :=
  bc19_menger_minmax _ _ _ sep_card

-- The hard direction on the path of four vertices.
example : Nonempty (bc16_DisjointPathFamily (SimpleGraph.pathGraph 4) Set.univ Set.univ (Fin 4)) :=
  bc19_hardDir_all _ _ _ 4 sep_card

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerFanPaths
