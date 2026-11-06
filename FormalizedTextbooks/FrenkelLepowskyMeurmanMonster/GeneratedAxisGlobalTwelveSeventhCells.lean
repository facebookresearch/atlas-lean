/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhFamily
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthCells

/-! Explicit cell words for the Seventh family: one product of original odd source letters
(at most two Xi letters) in each orbit of the Seventh forest. Kernel-checked binary transports in
the Seventh forest letters carry the forest roots to these cell roots, so the actual
decomposition and the triality reduction hold at the explicit cell words. The open vectors
below are explicit hypotheses, not asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Odd source letters of the explicit Seventh cell words (product order). -/
def seventhCellLetters : Fin 23 → List (Fin 10) :=
  ![[],
   [1, 6],
   [1, 6, 9],
   [1, 9],
   [0, 7, 9, 1, 6],
   [0, 9, 1, 7],
   [0, 7, 7, 9, 1, 6],
   [0, 9, 1, 6],
   [0, 9, 7, 1, 9, 6],
   [0, 6, 9, 1, 6, 6, 9],
   [0, 7, 7, 9, 1, 9],
   [1, 9, 7, 0, 9],
   [1, 7, 0, 9],
   [1, 9, 7, 0, 9, 6],
   [0, 9, 1, 7, 9],
   [1, 9, 1, 7, 7, 9],
   [1, 9, 1, 7],
   [0, 6, 9, 1, 9],
   [1, 6, 6],
   [0, 7, 1, 9, 6],
   [1, 9, 7, 9, 6, 6, 6, 9],
   [1, 7, 7],
   [1, 7, 9]]

/-- The explicit Seventh cell words, as actual local elements. -/
def seventhCellWord (i : Fin 23) : H :=
  ((seventhCellLetters i).map generatedAxisGlobalOddSourceLocalLetter).prod

/-- Binary root masks of the explicit Seventh cell words. -/
def seventhCellMask : Fin 23 → ℕ :=
  ![2048, 4198400, 7389184, 4243456, 51456, 985856, 379150, 2304, 6236, 13367, 592892, 990192,
    3056, 710748, 2302, 1032, 4201216, 6156, 4849664, 2140, 3751936, 4587520, 8372224]

/-- Words in the Seventh forest letters transporting the forest roots to the cell roots. -/
def seventhCellTransport : Fin 23 → List (Fin 4) :=
  ![[],
   [1, 0, 3, 0, 2, 1, 2, 0],
   [1, 3, 1, 2, 1, 0, 2],
   [2, 0, 3, 1, 0, 2, 0],
   [1, 0, 3, 0, 3, 0, 0, 2, 3, 3, 1, 3, 0],
   [1, 2, 0, 1, 3, 2, 3, 0, 1],
   [1, 2, 0, 2, 3, 1, 1, 0, 0, 0, 2],
   [1, 3, 1, 1, 0, 0, 3, 0, 0],
   [2, 0, 0, 3, 2, 3, 3, 1, 2, 1, 0, 1],
   [0, 1, 3, 1, 1, 1, 1, 2, 0, 3, 0, 0],
   [2, 1, 3, 3, 2, 3, 3, 1],
   [0, 3, 1, 0, 0, 3, 0, 2, 0, 1, 0],
   [3, 2, 3, 0, 2, 1, 3, 1, 0, 0],
   [3, 0, 3, 3, 2, 1, 0, 1, 0],
   [1, 0, 0, 2, 1, 2, 0],
   [3, 0, 0, 3, 3, 1, 1, 1, 3, 1, 3],
   [3, 2, 1, 2, 3, 3, 2, 0],
   [1, 3, 2, 1, 0, 0, 3, 1, 2],
   [0, 1, 3, 2, 0, 2, 1, 0],
   [2, 0, 3, 2, 3, 2, 3, 2, 0],
   [3, 1, 0, 0],
   [3, 1, 2, 0],
   [0, 3, 2, 0, 1, 0]]

set_option maxRecDepth 100000 in
-- Kernel check of the 23 cell-word binary roots.
/-- Every Seventh cell word sends its displayed root mask to Ω. -/
theorem seventhCellWord_root_certificate : ∀ i : Fin 23,
    (seventhCellLetters i).foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) (seventhCellMask i) = 2048 := by
  decide +kernel

/-- The binary root of every Seventh cell word is its displayed mask. -/
theorem seventhCellWord_root (i : Fin 23) :
    (generatedAxisGlobalBinaryRoot (seventhCellWord i)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (seventhCellMask i) :=
  generatedAxisGlobalTwelveOddLetterProduct_root _ _ (seventhCellWord_root_certificate i)

set_option maxRecDepth 100000 in
-- Kernel check of the 23 binary transports in the forest letters.
/-- The forest-letter words carry each forest root mask to the cell root mask. -/
theorem seventhCellTransport_certificate : ∀ i : Fin 23,
    seventhBitsetWordApply (seventhCellTransport i)
      (generatedAxisGlobalTwelveSeventhLongRootMask i) = seventhCellMask i := by
  decide +kernel

/-- Each transport word is an actual whole-axis fixer moving the forest root to the cell root. -/
theorem seventhCellTransport_lift (i : Fin 23) :
    ∃ h : H, h ∈ generatedSeventhLocalAxisStabilizer ∧
      generatedAxisGlobalBinaryAct h
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSeventhRootWord i)) =
        generatedAxisGlobalBinaryRoot (seventhCellWord i) := by
  have hmem : seventhBitsetWord (seventhCellTransport i) ∈
      generatedSeventhProjectedAxisStabilizer := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact seventhForestLetter_mem g
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h.val, h.property, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH h.val)
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSeventhRootWord i)).val = _
  have hh' : projH h.val = seventhBitsetWord (seventhCellTransport i) := hh
  rw [hh', generatedAxisGlobalTwelveSeventhRootWord_root, seventhCellWord_root,
    seventhBitsetWord_action, seventhCellTransport_certificate]

/-- The actual binary Ω orbit is covered by the stabilizer images of the cell roots. -/
theorem seventhCell_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 23, ∃ c : H,
      c ∈ generatedSeventhLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (seventhCellWord i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalTwelveSeventh_actual_binary_cover x
  obtain ⟨h, hh, hr⟩ := seventhCellTransport_lift i
  refine ⟨i, c * h⁻¹, Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hh), ?_⟩
  rw [← hr, ← generatedAxisGlobalBinaryAct_mul, mul_assoc, inv_mul_cancel, mul_one]
  exact he

/-- Every actual local element admits a phase-correct transition decomposition at the
explicit Seventh cell words. -/
theorem seventhCell_actual_decompose (h : H) :
    ∃ i : Fin 23, ∃ k c : H, k ∈ localOmegaStabilizer ∧ c ∈ generatedSeventhLocalAxisStabilizer ∧
      (h = k * seventhCellWord i * c ∨ h = k * (inclQ singletonCocodeQ * seventhCellWord i) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedSeventhLocalAxisStabilizer seventhCellWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedSeventhLocalAxisStabilizer
      seventhCellWord seventhCell_binary_cover) h

/-- Memberships of both triality images at every Seventh cell word suffice for the family. -/
theorem seventhCell_triality_of_actual_destinations {ι : Type*} (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 23,
      sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈ generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 23,
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈ generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedSeventhAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, k, c, hk, hc, he⟩ := seventhCell_actual_decompose h
  have hfix : rhoLocal c generatedSeventhAxis = generatedSeventhAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨k, hk⟩
      (rhoLocal (seventhCellWord i) generatedSeventhAxis)
    rw [← hm]
    exact generatedLocalOrbitUnion_local v m (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨k, hk⟩
      (rhoLocal (inclQ singletonCocodeQ * seventhCellWord i) generatedSeventhAxis)
    rw [← hm]
    apply generatedLocalOrbitUnion_local v m
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

/-- The cocode index of the actual Seventh-axis Q fixer used at each merged cell. -/
def seventhCellPhaseFixer : Fin 23 → Fin 4 :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

set_option maxHeartbeats 4000000 in
-- Check the odd root pairings of the actual Q fixers at the merged cells.
/-- The actual Seventh-axis Q fixers have odd pairing with the merged cell root masks. -/
theorem seventhCellPhaseFixer_pairing : ∀ i : Fin 23,
    i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23)) →
    qBeta (binaryCocodeEmbedding (generatedSeventhRootQModulation (seventhCellPhaseFixer i)))
        (monsterCo1GeometryBinaryMaskDecode (seventhCellMask i)) +
      qBeta (monsterCo1GeometryBinaryMaskDecode (seventhCellMask i))
        (binaryCocodeEmbedding
          (generatedSeventhRootQModulation (seventhCellPhaseFixer i))) = 1 := by
  decide +kernel

/-- At the merged cells both actual triality signs give the same local class. -/
theorem seventhCell_phase_merge (i : Fin 23)
    (hi : i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23))) :
    ∃ k : H, sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge generatedSeventhAxis _
    (cocodeQ (generatedSeventhRootQModulation (seventhCellPhaseFixer i)))
    (generatedSeventh_root_Q_mem _)
  rw [seventhCellWord_root]
  exact seventhCellPhaseFixer_pairing i hi

/-- Seventh cells whose positive transition is not yet bound to the catalogue. -/
def seventhCellOpenPositive : Finset (Fin 23) :=
  Finset.univ.erase 0

/-- Seventh cells whose inverse transition is neither bound nor phase merged. -/
def seventhCellOpenNegative : Finset (Fin 23) :=
  {1, 2, 3, 10, 11, 12, 17, 18, 20, 21, 22}

/-- Triality coverage of the actual Seventh family from the open vectors at the explicit
cell words. -/
theorem generatedAxisGlobalTwelve_seventh_covered_of_cells
    (hpos : ∀ i ∈ seventhCellOpenPositive,
      sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ seventhCellOpenNegative,
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 6 := by
  have h0 : seventhCellWord 0 = generatedAxisGlobalTwelveSeventhRootWord 0 := rfl
  have hp : ∀ i : Fin 23,
      sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases hi : i = 0
    · rw [hi, h0]
      exact generatedAxisGlobalTwelveSeventh_root00_positive
    · exact hpos i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hn : ∀ i : Fin 23,
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases hi : i = 0
    · rw [hi, h0]
      exact generatedAxisGlobalTwelveSeventh_root00_negative
    by_cases hm : i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23))
    · obtain ⟨k, hk⟩ := seventhCell_phase_merge i hm
      have he : sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) =
          rhoLocal k⁻¹ (sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis)) := by
        rw [hk, map_inv]
        exact (LinearEquiv.symm_apply_apply _ _).symm
      rw [he]
      exact generatedLocalOrbitUnion_local _ _ (hp i)
    · apply hneg
      fin_cases i <;> simp_all [seventhCellOpenNegative]
  intro h
  rw [generatedAxisGlobalTwelveSeventh_rep_seventh]
  exact seventhCell_triality_of_actual_destinations _ hp hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
