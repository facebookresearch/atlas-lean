/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.KWGeometricDual









open scoped BigOperators
open Finset

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section



theorem kwg_indexedCut_fiber_card (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P))
    (hF : kwg_IsEven (kwg_dualEnds P) F) :
    ((Finset.univ.filter (fun config : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) config = F)).card : Real) =
      (2 : Real) ^ Nat.card P.G.ConnectedComponent := by
  classical
  obtain ⟨config, hconfig⟩ :=
    (kwg_geometricCutCycleDuality P F).mp hF
  have hfilter :
      Finset.univ.filter (fun other : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) other = F) =
        Finset.univ.filter (fun other : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) other =
            kwg_cutSet (kwg_primalEnds P) config) := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hconfig]
  rw [hfilter, kwg_primalCut_fiber_card]
  norm_num



theorem kwg_weightedCutEvenSum (P : PlanarZ2Subgraph)
    (observable : Finset (kwg_Edge P) -> Real) :
    (∑ config : ConfigSpace P.V,
        observable (kwg_cutSet (kwg_primalEnds P) config)) =
      (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        ∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then observable F else 0 := by
  classical
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset (ConfigSpace P.V)))
    (g := fun config => kwg_cutSet (kwg_primalEnds P) config)
    (f := fun config =>
      observable (kwg_cutSet (kwg_primalEnds P) config))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  have hinner :
      (∑ config ∈ (Finset.univ : Finset (ConfigSpace P.V)) with
          kwg_cutSet (kwg_primalEnds P) config = F,
          observable (kwg_cutSet (kwg_primalEnds P) config)) =
        ((Finset.univ.filter (fun config : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) config = F)).card : Real) *
          observable F := by
    calc
      _ = ∑ _config ∈
          (Finset.univ.filter (fun config : ConfigSpace P.V =>
            kwg_cutSet (kwg_primalEnds P) config = F)), observable F := by
        apply Finset.sum_congr rfl
        intro config hconfig
        rw [(Finset.mem_filter.mp hconfig).2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hinner]
  by_cases hF : kwg_IsEven (kwg_dualEnds P) F
  · rw [if_pos hF, kwg_indexedCut_fiber_card P F hF]
  · rw [if_neg hF, mul_zero]
    have hempty :
        Finset.univ.filter (fun config : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) config = F) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro config _ hconfig
      exact hF ((kwg_geometricCutCycleDuality P F).mpr ⟨config, hconfig⟩)
    rw [hempty, Finset.card_empty]
    norm_num

end

end StatMech.Onsager
