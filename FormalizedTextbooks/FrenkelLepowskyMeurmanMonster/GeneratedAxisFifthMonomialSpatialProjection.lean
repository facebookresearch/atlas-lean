/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSpatialWords

/-! The six original local words have their genuine physical coordinate actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every literal source word projects to its actual Golay permutation word. -/
theorem generatedFifth_monomial_word_spatial (w : List (Fin 2 × Bool)) :
    generatedFourthMonomialSpatialProjection
        ((w.map generatedFourthMonomialFiberLetter).prod) =
      golayPermutationHom ((w.map generatedFourthMonomialPermutationLetter).prod) := by
  rw [map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  exact generatedFourth_monomial_letter_spatial l

/-- The selected coordinate transport uses the actual original spatial action. -/
theorem generatedFifth_monomial_transport_spatial :
    generatedFifthMonomialTransportFiber.val.2 =
      golayPermutationIsometry generatedFifthMonomialTransportPermutation := by
  change generatedFourthMonomialSpatialProjection generatedFifthMonomialTransportFiber =
    golayPermutationHom generatedFifthMonomialTransportPermutation
  exact generatedFifth_monomial_word_spatial generatedFifthMonomialTransportWord

/-- Each conjugated source lift has precisely its proved physical coordinate permutation. -/
theorem generatedFifth_monomial_spatial (k : Fin 6) :
    (generatedFifthMonomialSpatialFiber k).val.2 =
      golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k) := by
  change generatedFourthMonomialSpatialProjection (generatedFifthMonomialSpatialFiber k) =
    golayPermutationHom (generatedFifthMonomialSpatialPermutation k)
  have ht : generatedFourthMonomialSpatialProjection generatedFifthMonomialTransportFiber =
      golayPermutationHom generatedFifthMonomialTransportPermutation :=
    generatedFifth_monomial_transport_spatial
  unfold generatedFifthMonomialSpatialFiber generatedFifthMonomialSpatialPermutation
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
    generatedFifth_monomial_word_spatial, ht]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
