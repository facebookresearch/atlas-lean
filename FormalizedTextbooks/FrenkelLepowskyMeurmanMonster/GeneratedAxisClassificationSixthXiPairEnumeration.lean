/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairCoordinates

/-! Original physical pair-source enumeration covers genuine pair labels
without assuming index order. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The lexicographic physical address; this is independent of the intrinsic pair-index order. -/
def generatedSixthXiPairPhysicalRank (a b : Fin 24) : ℕ :=
  a.val * (47 - a.val) / 2 + (b.val - a.val - 1)

/-- A bounded source-list lookup from sorted physical coordinates and their preferred sign. -/
def generatedSixthXiPairPhysicalLookup (s : Fin 2) (a b : Fin 24) : Fin 552 :=
  ⟨2 * (generatedSixthXiPairPhysicalRank a b % 276) + s.val, by omega⟩

set_option maxHeartbeats 8000000 in
-- Check the finite physical lookup against every original sorted coordinate pair and sign.
/-- Every sorted physical pair has its exact original source-list entry. -/
theorem generatedSixth_xi_pair_physical_lookup : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → generatedSixthXiPairSourceCoordinates
      (generatedSixthXiPairPhysicalLookup s a b) = (s, a, b) := by
  decide +kernel

/-- Every genuine signed pair coordinate occurs as an original source. -/
theorem generatedSixth_xi_pair_input_surjective (s : Fin 2) (p : Fin 276) :
    ∃ j : Fin 552, generatedSixthXiPairInput j = Sum.inl (s, p) := by
  let a := (griessCoordinatePair p).1
  let b := (griessCoordinatePair p).2
  have hab : a < b := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  refine ⟨generatedSixthXiPairPhysicalLookup s a b, ?_⟩
  rw [generatedSixthXiPairInput, generatedSixth_xi_pair_physical_lookup s a b hab]
  simp only [generatedSixthXiPairShort, dite_eq_left (ne_of_lt hab)]
  rw [griessPairIndex_pair]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
