/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPreferredPairData

/-! The ordered finite table is the genuine preferred pair catalogue: check its entries and
 order, then use uniqueness of sorted lists rather than reducing the sorting algorithm. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check the finite table's complete entries, absence of repetitions and original order.
/-- The original preferred sorted list is precisely the displayed physical coordinate table. -/
theorem generatedNinth_preferred_pair_list_actual :
    generatedNinthPreferredPairList = List.ofFn generatedNinthCoordinatePairData := by
  have hc : (List.ofFn generatedNinthCoordinatePairData).toFinset = griessCoordinatePairs := by
    decide +kernel
  have hn : (List.ofFn generatedNinthCoordinatePairData).Nodup := by
    decide +kernel
  have hp : (List.ofFn generatedNinthCoordinatePairData).Pairwise
      generatedNinthPairCoordinateLE := by
    decide +kernel
  have : IsTrans (Fin 24 × Fin 24) generatedNinthPairCoordinateLE :=
    ⟨fun _ _ _ h h' => Nat.le_trans h h'⟩
  have : Std.Antisymm generatedNinthPairCoordinateLE := ⟨fun _ _ h h' =>
    finProdFinEquiv.injective (Fin.ext (Nat.le_antisymm h h'))⟩
  have : Std.Total generatedNinthPairCoordinateLE := ⟨fun _ _ => Nat.le_total _ _⟩
  unfold generatedNinthPreferredPairList
  rw [← hc]
  exact (List.toFinset_sort generatedNinthPairCoordinateLE hn).mpr hp

/-- The displayed physical pairs are exactly the genuine preferred sorted coordinate pairs. -/
theorem generatedNinth_coordinate_pair_actual (p : Fin 276) :
    griessCoordinatePair p = generatedNinthCoordinatePairData p := by
  simp only [griessCoordinatePair, griessCoordinatePairEquiv, OrderIso.coe_toEquiv,
    Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  have hl : generatedNinthPreferredPairList.length = 276 := by
    rw [generatedNinth_preferred_pair_list_actual, List.length_ofFn]
  change generatedNinthPreferredPairList[p]'(by rw [hl]; exact p.isLt) =
    generatedNinthCoordinatePairData p
  simp only [generatedNinth_preferred_pair_list_actual, Fin.getElem_fin, List.getElem_ofFn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
