/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadSparseCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPreferredMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortOctads

/-! Genuine occurring octad families and their complete preferred-Q source masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The first occupied original source provides each genuine occurring octad family. -/
def generatedSeventhXiOctadReference (g : Fin 231) : Fin 2 × Fin 276 :=
  generatedSeventhXiOddSource
    ⟨generatedSeventhXiOctadEntries g 0, generatedSeventhXiOctad_first g⟩

/-- Every reference is an original octad source with exactly the stated full code label. -/
theorem generatedSeventhXiOctadReference_kind (g : Fin 231) :
    generatedSeventhXiShortDescriptor (generatedSeventhXiOctadReference g).1
      (generatedSeventhXiOctadReference g).2 0 = 1 ∧
    generatedSeventhXiOctadCodes g =
      generatedSeventhXiShortDescriptor (generatedSeventhXiOctadReference g).1
        (generatedSeventhXiOctadReference g).2 1 := by
  have h := generatedSeventhXiOctad_entry g 0
  rw [dite_eq_left (generatedSeventhXiOctad_first g)] at h
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- The complete finite source code label of an occurring octad family. -/
def generatedSeventhXiOctadCode (g : Fin 231) : Fin 4096 :=
  ⟨generatedSeventhXiOctadCodes g, by
    rw [(generatedSeventhXiOctadReference_kind g).2]
    exact (generatedSeventhXiShort_octad_data _ _
      (generatedSeventhXiOctadReference_kind g).1).1⟩

/-- The actual catalogue octad selected by the checked original source. -/
def generatedSeventhXiOctadFamily (g : Fin 231) : Fin 759 :=
  generatedSeventhXiShortOutputOctad (generatedSeventhXiOctadReference g).1
    (generatedSeventhXiOctadReference g).2 (generatedSeventhXiOctadReference_kind g).1

/-- The genuine catalogue family has the stated full source code. -/
theorem generatedSeventhXiOctadFamily_code (g : Fin 231) :
    golayOctadLabel (generatedSeventhXiOctadFamily g) = generatedSeventhXiOctadCode g := by
  apply Fin.ext
  rw [generatedSeventhXiOctadFamily, generatedSeventhXiShortOutputOctad_code]
  exact (generatedSeventhXiOctadReference_kind g).2.symm

/-- The original increasing physical coordinates of a genuine occurring octad. -/
def generatedSeventhXiOctadCoordinates (g : Fin 231) : Fin 8 → Fin 24 :=
  generatedSeventhXiShortOctadCoordinates (generatedSeventhXiOctadReference g).1
    (generatedSeventhXiOctadReference g).2

/-- Each physical coordinate is the original actual catalogue coordinate. -/
theorem generatedSeventhXiOctadCoordinates_actual (g : Fin 231) (k : Fin 8) :
    golayOctadCoordinate (generatedSeventhXiOctadFamily g) k =
      generatedSeventhXiOctadCoordinates g k := by
  exact generatedSeventhXiShortOutputOctad_coordinates _ _ _ k

/-- All negative physical positions retain the original normalized sixty-four-sign convention. -/
def generatedSeventhXiOctadNegativeMask (g : Fin 231) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedSeventhXiOctadCoordinates g k).val else 0) ||| m) 0

/-- The finite physical mask is exactly the genuine preferred octad sign mask. -/
theorem generatedSeventhXiOctadNegativeMask_actual (g : Fin 231) (e : Fin 64) :
    griessOctadSignMask (generatedSeventhXiOctadFamily g) e =
      generatedSeventhXiOctadNegativeMask g e := by
  simp only [griessOctadSignMask, generatedSeventhXiOctadNegativeMask,
    generatedSeventhXiOctadCoordinates_actual]

/-- Every occurring family's preferred lift has its complete finite source mask. -/
def generatedSeventhXiOctadPreferredMask (g : Fin 231) (e : Fin 64) : ℕ :=
  generatedSeventhXiShortQJoinMask
    (generatedSeventhXiShortTranslationMask (generatedSeventhXiOctadCode g)
      (griessOctadOmegaCoefficient e))
    (generatedSeventhXiShortModulationMask (generatedSeventhXiOctadCode g)
      (generatedSeventhXiOctadNegativeMask g e))

/-- The mask is the entire original preferred-Q element, with its zero central coefficient. -/
theorem generatedSeventhXiOctadPreferredMask_actual (g : Fin 231) (e : Fin 64) :
    griessShortQ (Sum.inr (Sum.inl (generatedSeventhXiOctadFamily g, e))) =
      generatedSeventhXiShortQMask (generatedSeventhXiOctadPreferredMask g e) := by
  rw [generatedSeventhXiShortOctadMask_actual, generatedSeventhXiOctadFamily_code,
    generatedSeventhXiOctadNegativeMask_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
