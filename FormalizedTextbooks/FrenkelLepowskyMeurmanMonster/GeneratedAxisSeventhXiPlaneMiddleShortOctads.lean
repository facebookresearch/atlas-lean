/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortArithmeticCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortOrder

/-! Actual octad catalogue identities follow from the certified physical code masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each octad descriptor has a genuine code octad and its increasing physical coordinates. -/
theorem generatedSeventhXiShort_octad_data (s : Fin 2) (p : Fin 276)
    (hk : generatedSeventhXiShortDescriptor s p 0 = 1) :
    generatedSeventhXiShortDescriptor s p 1 < 4096 ∧
    golayMaskWeight (golayEncodedMask (generatedSeventhXiShortDescriptor s p 1)) = 8 ∧
    generatedSeventhXiShortDescriptor s p 2 < 64 ∧
    StrictMono (generatedSeventhXiShortOctadCoordinates s p) ∧
    (∀ i : Fin 24, (golayEncodedMask (generatedSeventhXiShortDescriptor s p 1)).testBit i.val =
      true ↔ ∃ k, generatedSeventhXiShortOctadCoordinates s p k = i) := by
  have h := (generatedSeventhXiShort_shapes s p).2.2
  simp only [hk, show (1 : ℕ) ≠ 0 from by decide, ite_false, ite_true] at h
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  intro k l hkl
  exact h.2.2.2.1 k l hkl

/-- The intrinsic actual octad catalogue member selected by the genuine weight-eight code label. -/
def generatedSeventhXiShortOutputOctad (s : Fin 2) (p : Fin 276)
    (hk : generatedSeventhXiShortDescriptor s p 0 = 1) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨⟨generatedSeventhXiShortDescriptor s p 1, (generatedSeventhXiShort_octad_data s p hk).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (generatedSeventhXiShort_octad_data s p hk).2.1⟩⟩

/-- The selected actual catalogue member has exactly the checked source code label. -/
theorem generatedSeventhXiShortOutputOctad_code (s : Fin 2) (p : Fin 276)
    (hk : generatedSeventhXiShortDescriptor s p 0 = 1) :
    golayOctadLabel (generatedSeventhXiShortOutputOctad s p hk) =
      ⟨generatedSeventhXiShortDescriptor s p 1,
        (generatedSeventhXiShort_octad_data s p hk).1⟩ :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply _)

/-- The actual ordered octad coordinates equal the certified physical coordinate list. -/
theorem generatedSeventhXiShortOutputOctad_coordinates (s : Fin 2) (p : Fin 276)
    (hk : generatedSeventhXiShortDescriptor s p 0 = 1) (k : Fin 8) :
    golayOctadCoordinate (generatedSeventhXiShortOutputOctad s p hk) k =
      generatedSeventhXiShortOctadCoordinates s p k := by
  apply generatedSeventhXi_ordered_coordinates
  · exact (generatedSeventhXiShort_octad_data s p hk).2.2.2.1
  · intro i
    simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [generatedSeventhXiShortOutputOctad_code]
    exact (generatedSeventhXiShort_octad_data s p hk).2.2.2.2 i

/-- Physical sign masks keep the actual sixty-four-state octad convention. -/
theorem generatedSeventhXiShortOutputOctad_sign (s : Fin 2) (p : Fin 276)
    (hk : generatedSeventhXiShortDescriptor s p 0 = 1) :
    griessOctadSignMask (generatedSeventhXiShortOutputOctad s p hk)
      ⟨generatedSeventhXiShortDescriptor s p 2 % 64, Nat.mod_lt _ (by decide)⟩ =
        generatedSeventhXiShortNegativeMask s p := by
  simp only [griessOctadSignMask, generatedSeventhXiShortOutputOctad_coordinates,
    generatedSeventhXiShortNegativeMask]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
