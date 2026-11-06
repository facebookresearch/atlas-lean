/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSourceOctadOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSpatialProjection

/-! The full source-octad permutation group transported into the selected fifth coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original physical transport sends the source word14 to the actual selected word2052. -/
theorem generatedFifthMonomialTransport_octad :
    golayPermute generatedFifthMonomialTransportPermutation.val
        (golayEncoder (golayLabelCoefficients 14)) =
      golayOctadWord generatedFifthFlagOctad := by
  funext i
  rw [generatedFifth_flag_word_coordinate]
  revert i
  decide +kernel

/-- The full genuine permutation group of the selected octad, as actual conjugated source words. -/
def generatedFifthSelectedOctadSubgroup : Subgroup golayAutomorphismSubgroup :=
  generatedFifthSourceOctadSubgroup.map
    (MulAut.conj generatedFifthMonomialTransportPermutation).toMonoidHom

/-- Conjugating the actual source-octad stabilizer transports its exact word condition. -/
theorem generatedFifthSourceOctad_conjugate_mem (c p : golayAutomorphismSubgroup)
    (w : Fin 24 → ZMod 2)
    (hc : golayPermute c.val (golayEncoder (golayLabelCoefficients 14)) = w) :
    p ∈ generatedFifthSourceOctadSubgroup.map (MulAut.conj c).toMonoidHom ↔
      golayPermute p.val w = w := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change golayPermute (c.val * q.val * c.val⁻¹) w = w
    rw [← hc, golayPermute_mul, golayPermute_mul, golayPermute_inv, hq]
  · intro hp
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * p * c, ?_, ?_⟩
    · have h := congrArg (golayPermute c.val⁻¹) hp
      rw [← hc] at h
      simp only [← golayPermute_mul, inv_mul_cancel, golayPermute_one] at h
      exact h
    · change c * (c⁻¹ * p * c) * c⁻¹ = p
      simp [mul_assoc]

/-- Membership is exactly preservation of the actual selected Golay word. -/
theorem generatedFifthSelectedOctadSubgroup_mem (p : golayAutomorphismSubgroup) :
    p ∈ generatedFifthSelectedOctadSubgroup ↔
      golayPermute p.val (golayOctadWord generatedFifthFlagOctad) =
        golayOctadWord generatedFifthFlagOctad :=
  generatedFifthSourceOctad_conjugate_mem generatedFifthMonomialTransportPermutation p
    (golayOctadWord generatedFifthFlagOctad) generatedFifthMonomialTransport_octad

/-- The five actual generators of the full selected-octad permutation group. -/
def generatedFifthSelectedOctadPermutation (k : Fin 5) : golayAutomorphismSubgroup :=
  generatedFifthMonomialTransportPermutation * generatedFifthSourceOctadPermutation k *
    generatedFifthMonomialTransportPermutation⁻¹

/-- Literal physical coordinate arrays of the five genuine selected generators. -/
def generatedFifthSelectedOctadForward : Fin 5 → Fin 24 → Fin 24 :=
  ![![18, 1, 19, 3, 7, 9, 8, 4, 6, 5, 11, 10, 12, 23, 14, 20, 16, 17, 0, 2, 15, 21, 22, 13],
    ![0, 2, 1, 3, 4, 7, 6, 5, 21, 20, 22, 23, 13, 12, 14, 15, 17, 16, 18, 19, 9, 8, 10, 11],
    ![2, 3, 0, 1, 7, 6, 5, 4, 8, 9, 10, 11, 13, 12, 15, 14, 16, 17, 18, 19, 21, 20, 23, 22],
    ![0, 1, 2, 18, 9, 13, 22, 7, 8, 4, 15, 21, 12, 5, 20, 10, 17, 16, 3, 19, 14, 11, 6, 23],
    ![1, 19, 2, 17, 12, 15, 21, 20, 5, 10, 4, 8, 23, 13, 14, 22, 18, 0, 3, 16, 11, 9, 7, 6]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Bind all 120 physical coordinate images to the actual original word products.
/-- Each displayed selected-generator array is its genuine physical permutation. -/
theorem generatedFifthSelectedOctad_forward : ∀ k : Fin 5, ∀ i : Fin 24,
    (generatedFifthSelectedOctadPermutation k).val i = generatedFifthSelectedOctadForward k i := by
  decide +kernel

/-- Each original selected generator lies in the full actual selected-octad permutation group. -/
theorem generatedFifthSelectedOctad_generator_mem (k : Fin 5) :
    generatedFifthSelectedOctadPermutation k ∈ generatedFifthSelectedOctadSubgroup :=
  Subgroup.mem_map.mpr ⟨generatedFifthSourceOctadPermutation k,
    generatedFifthSourceOctad_generator_mem k, rfl⟩

/-- The actual selected-octad permutation group has the exact transported order 322560. -/
theorem generatedFifthSelectedOctad_card :
    Nat.card generatedFifthSelectedOctadSubgroup = 322560 := by
  unfold generatedFifthSelectedOctadSubgroup
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective generatedFifthSourceOctadSubgroup
    (MulAut.conj generatedFifthMonomialTransportPermutation).toMonoidHom
    (MulAut.conj generatedFifthMonomialTransportPermutation).injective).toEquiv]
  exact generatedFifthSourceOctad_card

/-- Inclusion of the five actual selected words includes the full actual selected-octad group. -/
theorem generatedFifthSelectedOctad_le_of_generators (P : Subgroup golayAutomorphismSubgroup)
    (hP : ∀ k : Fin 5, generatedFifthSelectedOctadPermutation k ∈ P) :
    generatedFifthSelectedOctadSubgroup ≤ P := by
  apply (Subgroup.map_le_iff_le_comap).mpr
  apply generatedFifthSourceOctad_le_of_generators
  exact hP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
