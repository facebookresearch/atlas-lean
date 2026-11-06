/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthFamily
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthForestCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords

/-! Explicit cell words for the Sixth family: one product of original odd source letters
(at most two Xi letters) in each orbit of the Sixth forest. Kernel-checked binary transports in
the Sixth forest letters carry the forest roots to these cell roots, so the actual
decomposition and the triality reduction hold at the explicit cell words. The open vectors
below are explicit hypotheses, not asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Odd source letters of the explicit Sixth cell words (product order). -/
def sixthCellLetters : Fin 10 → List (Fin 10) :=
  ![[],
   [1, 6],
   [1, 9],
   [0, 9, 1, 7, 7, 7],
   [0, 9, 1, 6],
   [0, 9, 1, 7],
   [1, 9, 1, 7],
   [1, 9, 6, 9, 1, 6],
   [1, 6, 6, 9],
   [1, 9, 1, 7, 7, 7]]

/-- The explicit Sixth cell words, as actual local elements. -/
def sixthCellWord (i : Fin 10) : H :=
  ((sixthCellLetters i).map generatedAxisGlobalOddSourceLocalLetter).prod

/-- Binary root masks of the explicit Sixth cell words. -/
def sixthCellMask : Fin 10 → ℕ :=
  ![2048, 4198400, 4243456, 117260, 2304, 985856, 4201216, 705793, 8175616, 383500]

/-- Words in the Sixth forest letters transporting the forest roots to the cell roots. -/
def sixthCellTransport : Fin 10 → List (Fin 15) :=
  ![[],
   [11, 14, 13, 10, 7, 12, 10],
   [12, 12, 14, 10, 6],
   [14, 11, 14, 13, 12, 3, 14, 12, 1],
   [13, 12, 14, 12, 7, 12, 0],
   [13, 10, 13, 10],
   [12, 13, 12, 5, 10],
   [11, 14, 12, 13, 4, 14, 5],
   [12, 12, 14, 10, 7],
   [10, 2, 13, 10, 0]]

/-- The binary action of a product of odd source letters is the composite of the letter rows. -/
theorem generatedAxisGlobalTwelveOddLetterProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

/-- A binary computation sending a mask to Ω identifies the binary root of a letter product. -/
theorem generatedAxisGlobalTwelveOddLetterProduct_root (ls : List (Fin 10)) (m : ℕ)
    (h : ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) m = 2048) :
    (generatedAxisGlobalBinaryRoot ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) m := by
  have hf : co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode m) = Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
    rw [generatedAxisGlobalTwelveOddLetterProduct_binary, h,
      generatedAxisGlobalTwelveSixth_omega_mask]
  change co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)⁻¹)
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← hf, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

set_option maxRecDepth 100000 in
-- Kernel check of the 10 cell-word binary roots.
/-- Every Sixth cell word sends its displayed root mask to Ω. -/
theorem sixthCellWord_root_certificate : ∀ i : Fin 10,
    (sixthCellLetters i).foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) (sixthCellMask i) = 2048 := by
  decide +kernel

/-- The binary root of every Sixth cell word is its displayed mask. -/
theorem sixthCellWord_root (i : Fin 10) :
    (generatedAxisGlobalBinaryRoot (sixthCellWord i)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (sixthCellMask i) :=
  generatedAxisGlobalTwelveOddLetterProduct_root _ _ (sixthCellWord_root_certificate i)

set_option maxRecDepth 100000 in
-- Kernel check of the 10 binary transports in the forest letters.
/-- The forest-letter words carry each forest root mask to the cell root mask. -/
theorem sixthCellTransport_certificate : ∀ i : Fin 10,
    sixthBitsetWordApply (sixthCellTransport i)
      (generatedAxisGlobalTwelveSixthLongRootMask i) = sixthCellMask i := by
  decide +kernel

/-- Each transport word is an actual whole-axis fixer moving the forest root to the cell root. -/
theorem sixthCellTransport_lift (i : Fin 10) :
    ∃ h : H, h ∈ generatedSixthLocalAxisStabilizer ∧
      generatedAxisGlobalBinaryAct h
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSixthRootWord i)) =
        generatedAxisGlobalBinaryRoot (sixthCellWord i) := by
  have hmem : sixthBitsetWord (sixthCellTransport i) ∈
      generatedSixthProjectedAxisStabilizer := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact generatedAxisGlobalTwelveSixthGenerator_projected_mem g
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h.val, h.property, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH h.val)
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSixthRootWord i)).val = _
  have hh' : projH h.val = sixthBitsetWord (sixthCellTransport i) := hh
  rw [hh', generatedAxisGlobalTwelveSixthRootWord_root, sixthCellWord_root,
    sixthBitsetWord_action, sixthCellTransport_certificate]

/-- The actual binary Ω orbit is covered by the stabilizer images of the cell roots. -/
theorem sixthCell_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 10, ∃ c : H,
      c ∈ generatedSixthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (sixthCellWord i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalTwelveSixth_actual_binary_cover x
  obtain ⟨h, hh, hr⟩ := sixthCellTransport_lift i
  refine ⟨i, c * h⁻¹, Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hh), ?_⟩
  rw [← hr, ← generatedAxisGlobalBinaryAct_mul, mul_assoc, inv_mul_cancel, mul_one]
  exact he

/-- Every actual local element admits a phase-correct transition decomposition at the
explicit Sixth cell words. -/
theorem sixthCell_actual_decompose (h : H) :
    ∃ i : Fin 10, ∃ k c : H, k ∈ localOmegaStabilizer ∧ c ∈ generatedSixthLocalAxisStabilizer ∧
      (h = k * sixthCellWord i * c ∨ h = k * (inclQ singletonCocodeQ * sixthCellWord i) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedSixthLocalAxisStabilizer sixthCellWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedSixthLocalAxisStabilizer
      sixthCellWord sixthCell_binary_cover) h

/-- Memberships of both triality images at every Sixth cell word suffice for the family. -/
theorem sixthCell_triality_of_actual_destinations {ι : Type*} (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 10,
      sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈ generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 10,
      sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈ generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedSixthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, k, c, hk, hc, he⟩ := sixthCell_actual_decompose h
  have hfix : rhoLocal c generatedSixthAxis = generatedSixthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨k, hk⟩
      (rhoLocal (sixthCellWord i) generatedSixthAxis)
    rw [← hm]
    exact generatedLocalOrbitUnion_local v m (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨k, hk⟩
      (rhoLocal (inclQ singletonCocodeQ * sixthCellWord i) generatedSixthAxis)
    rw [← hm]
    apply generatedLocalOrbitUnion_local v m
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

/-- The cocode index of the actual Sixth-axis Q fixer used at each merged cell. -/
def sixthCellPhaseFixer : Fin 10 → Fin 4 :=
  ![1, 1, 1, 2, 1, 1, 1, 2, 1, 2]

set_option maxHeartbeats 4000000 in
-- Check the odd root pairings of the actual Q fixers at the merged cells.
/-- The actual Sixth-axis Q fixers have odd pairing with the merged cell root masks. -/
theorem sixthCellPhaseFixer_pairing : ∀ i : Fin 10,
    i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10)) →
    qBeta (binaryCocodeEmbedding (generatedSixthRootQModulation (sixthCellPhaseFixer i)))
        (monsterCo1GeometryBinaryMaskDecode (sixthCellMask i)) +
      qBeta (monsterCo1GeometryBinaryMaskDecode (sixthCellMask i))
        (binaryCocodeEmbedding
          (generatedSixthRootQModulation (sixthCellPhaseFixer i))) = 1 := by
  decide +kernel

/-- At the merged cells both actual triality signs give the same local class. -/
theorem sixthCell_phase_merge (i : Fin 10)
    (hi : i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10))) :
    ∃ k : H, sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge generatedSixthAxis _
    (cocodeQ (generatedSixthRootQModulation (sixthCellPhaseFixer i)))
    (generatedSixth_root_Q_mem _)
  rw [sixthCellWord_root]
  exact sixthCellPhaseFixer_pairing i hi

/-- Sixth cells whose positive transition is not yet bound to the catalogue. -/
def sixthCellOpenPositive : Finset (Fin 10) :=
  Finset.univ.erase 0

/-- Sixth cells whose inverse transition is neither bound nor phase merged. -/
def sixthCellOpenNegative : Finset (Fin 10) :=
  {1, 2, 8}

/-- Triality coverage of the actual Sixth family from the open vectors at the explicit
cell words. -/
theorem generatedAxisGlobalTwelve_sixth_covered_of_cells
    (hpos : ∀ i ∈ sixthCellOpenPositive,
      sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ sixthCellOpenNegative,
      sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 5 := by
  have h0 : sixthCellWord 0 = generatedAxisGlobalTwelveSixthRootWord 0 := rfl
  have hp : ∀ i : Fin 10,
      sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases hi : i = 0
    · rw [hi, h0]
      exact generatedAxisGlobalTwelveSixth_root00_positive
    · exact hpos i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hn : ∀ i : Fin 10,
      sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases hi : i = 0
    · rw [hi, h0]
      exact generatedAxisGlobalTwelveSixth_root00_negative
    by_cases hm : i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10))
    · obtain ⟨k, hk⟩ := sixthCell_phase_merge i hm
      have he : sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) =
          rhoLocal k⁻¹ (sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis)) := by
        rw [hk, map_inv]
        exact (LinearEquiv.symm_apply_apply _ _).symm
      rw [he]
      exact generatedLocalOrbitUnion_local _ _ (hp i)
    · apply hneg
      fin_cases i <;> simp_all [sixthCellOpenNegative]
  intro h
  rw [generatedAxisGlobalTwelveSixth_rep_sixth]
  exact sixthCell_triality_of_actual_destinations _ hp hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
