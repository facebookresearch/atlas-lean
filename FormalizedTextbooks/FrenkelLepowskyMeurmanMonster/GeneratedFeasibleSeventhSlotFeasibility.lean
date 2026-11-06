/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotFeasibility
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQConjugation
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative

/-! The counted seventh prototype is a genuine feasible axis for each of its three triangle
pair axes. This is the feasibility half of source slot 8 (label 6C1) of Höhn–Seysen,
arXiv:2508.01037, §4 and Table 3. The proof follows the literal triality, local and triality
word of the prototype, starting from the actual secondary feasible orbit of a source pair
axis. No orbit count or table value is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
-- Elaborate the subtype of the complete 93,150-address finite physical catalogue.
/-- Every actual signed short axis perpendicular to the root of a positive pair axis is
feasible for that pair axis. Coverage of the actual secondary orbit is transported from the
physical first root by a genuine local element. -/
theorem generatedFeasibleSeventhSlot_orthogonal_feasible (p : Fin 276) (r : GriessShortIndex)
    (c : ZMod 2)
    (hr : stdPairingFun (griessShortVector (Sum.inl (0, p))) (griessShortVector r) = 0) :
    conwayShortAxis r c ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1) := by
  obtain ⟨k, hk⟩ := generatedAxis_local_signed_transitive (Sum.inl (0, p))
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 0
  have hk1 := generatedFeasibleSixthSlot_local_opposite k _ _ hk
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup k
  change localFiberIntoH f = k at hf
  have hperm : griessShortPermutation f.val.2 (Sum.inl (0, p)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) := by
    have h := hk
    rw [← hf] at h
    change localGriessRepresentation f _ = _ at h
    rw [generatedAxis_localFiber_image] at h
    exact congrArg Prod.fst (@generatedAxis_signed_injective
      (griessShortPermutation f.val.2 (Sum.inl (0, p)), localShortPhase f (Sum.inl (0, p)) + 0)
      (Sum.inl (0, generatedFeasiblePhysicalRootPair), 0) h)
  have himage : rhoLocal k (conwayShortAxis r c) =
      conwayShortAxis (griessShortPermutation f.val.2 r) (localShortPhase f r + c) := by
    rw [← hf]
    exact generatedAxis_localFiber_image f _ _
  have horth := generatedFeasibleSixthSlot_image_orthogonal f.val.2 _ _ hr
  rw [hperm] at horth
  have hmem : griessShortPermutation f.val.2 r ∈ generatedFeasibleOrthogonalShortLabels := by
    rw [generatedFeasibleOrthogonalShortLabels_mem,
      ← generatedFeasiblePhysicalRoot_orthogonal_iff]
    exact horth
  have hsec : rhoLocal k (conwayShortAxis r c) ∈
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
    rw [generatedFeasibleSecondaryLocalOrbit_eq_physical, himage]
    exact ⟨⟨(_, _), Finset.mem_product.mpr ⟨hmem, Finset.mem_univ _⟩⟩, rfl⟩
  have hback := generatedFeasibleSixthSlot_orbit_local k⁻¹
    (generatedFeasibleSecondaryLocalOrbit_subset generatedFeasiblePhysicalRootPair hsec)
  rwa [generatedFeasibleSixthSlot_local_inverse k hk,
    generatedFeasibleSixthSlot_local_inverse k hk1,
    generatedFeasibleSixthSlot_local_inverse k (x := conwayShortAxis r c) rfl] at hback

/-- The literal odd short prototype is perpendicular to each of the three original source
roots, the minus pairs on physical coordinates twelve, fourteen and fifteen. -/
theorem generatedFeasibleSeventhSlot_source_root_orthogonal (j : Fin 3) :
    stdPairingFun (griessShortVector (Sum.inl (0, generatedSeventhSourcePair j)))
      (griessShortVector (Sum.inr (Sum.inr (0, 0)))) = 0 := by
  rw [griessShortVector_pairing]
  have h : leechIntegralPairing
      (griessShortIntegral (Sum.inl (0, generatedSeventhSourcePair j)))
      (griessShortIntegral (Sum.inr (Sum.inr (0, 0)))) = 0 := by
    simp only [griessShortIntegral, (generatedSeventh_pair_coordinate_certificate j).1]
    fin_cases j <;> decide +kernel
  rw [h]
  simp

/-- The literal seventh local word sends both signs of each source root axis to the
corresponding signs of the triangle root axis. -/
theorem generatedFeasibleSeventhSlot_local_root (j : Fin 3) (c : ZMod 2) :
    rhoLocal (localFiberIntoH generatedSeventhLocalFiber)
      (conwayShortAxis (Sum.inl (0, generatedSeventhSourcePair j)) c) =
        conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) c := by
  change localGriessRepresentation generatedSeventhLocalFiber _ = _
  rw [generatedAxis_localFiber_image, generatedSeventh_pair_permutation,
    generatedSeventh_pair_phase, zero_add]

/-- The counted seventh prototype is an actual feasible axis for each positive triangle root
axis: it lies in the orbit of the opposite axis under the full generated stabilizer. -/
theorem generatedFeasibleSeventhSlot_prototype_feasible_root (j : Fin 3) :
    generatedSeventhAxis ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) 0)
      (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair j)) 1) := by
  have hodd := generatedFeasibleSixthSlot_orbit_triality (generatedSeventhSourcePair j)
    (generatedFeasibleSeventhSlot_orthogonal_feasible _ _ 0
      (generatedFeasibleSeventhSlot_source_root_orthogonal j))
  have hmid := generatedFeasibleSixthSlot_orbit_local
    (localFiberIntoH generatedSeventhLocalFiber) hodd
  rw [generatedFeasibleSeventhSlot_local_root, generatedFeasibleSeventhSlot_local_root] at hmid
  rw [generatedSeventhAxis_local_expression]
  exact generatedFeasibleSixthSlot_orbit_triality (generatedSeventhTargetPair j) hmid

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
