/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusCoordinates
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarDeformation
public import MathlibExt.Topology.Category.TopPair.ClosedBall.AnnulusDeformation

/-!
# The actual family-annulus deformation and original attaching maps

The original family annulus deforms to its radius-five-eighths boundary
section while retaining every cell index. Its normalized direction is the
original literal NDR boundary retraction. Consequently its characteristic
map into the actual outer region, followed by the original-space
retraction, is the original attaching map of that normalized boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.CellAnnulusDeformation

variable {ι : Type u}

/-- The same original boundary direction supplied by the annulus coordinates. -/
def direction (ι : Type u) (n : ℕ) :
    C(CellCollarCover.annulus ι n, CellFamilyAttachment.boundaries ι n) :=
  TopPair.AnnulusCoordinates.directionMap (CellFamilyAttachment.boundaries ι n)
    (CellAnnulusCoordinates.homeomorph ι n)

theorem direction_eq_coordinates (ι : Type u) (n : ℕ) :
    direction ι n = CellAnnulusCoordinates.direction ι n :=
  rfl

/-- The actual radius-five-eighths section of the original boundary family. -/
def boundarySection (ι : Type u) (n : ℕ) :
    C(CellFamilyAttachment.boundaries ι n, CellCollarCover.annulus ι n) :=
  TopPair.AnnulusCoordinates.sectionMap (CellFamilyAttachment.boundaries ι n)
    (CellAnnulusCoordinates.homeomorph ι n)

theorem boundarySection_coordinates (n : ℕ) (b : CellFamilyAttachment.boundaries ι n) :
    boundarySection ι n b =
      CellAnnulusCoordinates.inverse ι n (b, TopPair.cellAnnulusMidRadius) :=
  rfl

theorem direction_boundarySection (n : ℕ) (b : CellFamilyAttachment.boundaries ι n) :
    direction ι n (boundarySection ι n b) = b :=
  TopPair.AnnulusCoordinates.direction_section (CellFamilyAttachment.boundaries ι n)
    (CellAnnulusCoordinates.homeomorph ι n) b

/-- The actual family annulus deforms to its original boundary section, fixed on that section. -/
def deformation (ι : Type u) (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (CellCollarCover.annulus ι n))
      ((boundarySection ι n).comp (direction ι n)) (Set.range (boundarySection ι n)) :=
  TopPair.AnnulusCoordinates.deformation (CellFamilyAttachment.boundaries ι n)
    (CellAnnulusCoordinates.homeomorph ι n)

theorem deformation_direction (n : ℕ) (t : I) (z : CellCollarCover.annulus ι n) :
    direction ι n (deformation ι n (t, z)) = direction ι n z :=
  TopPair.AnnulusCoordinates.deformation_direction (CellFamilyAttachment.boundaries ι n)
    (CellAnnulusCoordinates.homeomorph ι n) t z

/-- Every original cell index is retained during the actual annular deformation. -/
theorem deformation_index (n : ℕ) (t : I) (z : CellCollarCover.annulus ι n) :
    (deformation ι n (t, z)).1.1 = z.1.1 := by
  have h := congrArg Sigma.fst (deformation_direction n t z)
  simpa only [direction_eq_coordinates, CellAnnulusCoordinates.direction_index] using h

/-- The actual original disk norm follows the radius segment inside the overlap. -/
theorem deformation_norm (n : ℕ) (t : I) (z : CellCollarCover.annulus ι n) :
    CellCollarCover.diskNorm n (deformation ι n (t, z)).1 =
      (1 - (t : ℝ)) * CellCollarCover.diskNorm n z.1 +
        (t : ℝ) * (TopPair.cellAnnulusMidRadius : ℝ) := by
  have h := TopPair.AnnulusCoordinates.deformation_radius
    (CellFamilyAttachment.boundaries ι n) (CellAnnulusCoordinates.homeomorph ι n) t z
  change (CellAnnulusCoordinates.radius ι n (deformation ι n (t, z)) : ℝ) =
    (1 - (t : ℝ)) * (CellAnnulusCoordinates.radius ι n z : ℝ) +
      (t : ℝ) * (TopPair.cellAnnulusMidRadius : ℝ) at h
  simpa only [CellAnnulusCoordinates.radius_val] using h

/-- The genuine family annulus and original boundary sigma are homotopy equivalent. -/
def homotopyEquiv (ι : Type u) (n : ℕ) :
    ContinuousMap.HomotopyEquiv (CellCollarCover.annulus ι n)
      (CellFamilyAttachment.boundaries ι n) :=
  TopPair.AnnulusCoordinates.homotopyEquiv (CellFamilyAttachment.boundaries ι n)
    (CellAnnulusCoordinates.homeomorph ι n)

/-- The original annular point viewed in the same original controlled disk collar. -/
def controlledPoint (ι : Type u) (n : ℕ) :
    C(CellCollarCover.annulus ι n, (CellFamilyAttachment.ndrData ι n).neighborhood) where
  toFun z := ⟨z.1, by
    exact (CellFamilyAttachment.ndrData_control_lt_one_iff n z.1).mpr z.2.1⟩
  continuous_toFun := by
    exact continuous_subtype_val.subtype_mk (fun z => by
      exact (CellFamilyAttachment.ndrData_control_lt_one_iff n z.1).mpr z.2.1)

/-- The original radial NDR endpoint is the normalized original annular direction. -/
theorem ndrEndpoint_direction (n : ℕ) (z : CellCollarCover.annulus ι n) :
    (CellFamilyAttachment.ndrData ι n).endpoint z.1 =
      CellFamilyAttachment.boundaryToDisks ι n (direction ι n z) := by
  rcases z with ⟨⟨i, d⟩, hz⟩
  let z : CellCollarCover.annulus ι n := ⟨⟨i, d⟩, hz⟩
  rcases hDir : direction ι n z with ⟨j, b⟩
  have hIndex := CellAnnulusCoordinates.direction_index n z
  change (direction ι n z).1 = i at hIndex
  rw [hDir] at hIndex
  change j = i at hIndex
  subst j
  have hVector := CellAnnulusCoordinates.direction_val n z
  change (direction ι n z).2.down.val = ‖d.down.val‖⁻¹ • d.down.val at hVector
  rw [hDir] at hVector
  have hScale : TopPair.closedUnitBallRadialScale d.down.val = ‖d.down.val‖⁻¹ := by
    unfold TopPair.closedUnitBallRadialScale
    exact congrArg (fun r : ℝ => r⁻¹) (max_eq_left (le_of_lt hz.1))
  have hEndpoint := TopPair.closedUnitBallEndpoint_down_val (E := Fin (n + 1) → ℝ) d
  have hValue : ((classicalCellDiskPairNDRData.{u} (n + 1)).endpoint d).down.val =
      b.down.val :=
    hEndpoint.trans ((congrArg (fun r : ℝ => r • d.down.val) hScale).trans hVector.symm)
  rw [CellFamilyAttachment.ndrData_endpoint_component]
  change (⟨i, (classicalCellDiskPairNDRData.{u} (n + 1)).endpoint d⟩ :
      CellFamilyAttachment.disks ι n) =
    ⟨i, (classicalCellDiskPair.{u} (n + 1)).map b⟩
  apply congrArg (fun q : (classicalCellDiskPair.{u} (n + 1)).fst =>
    (⟨i, q⟩ : CellFamilyAttachment.disks ι n))
  apply ULift.down_injective
  apply Subtype.ext
  exact hValue

/-- The actual original boundary retraction agrees with the proved annular direction. -/
theorem controlledRetraction_direction (n : ℕ) (z : CellCollarCover.annulus ι n) :
    CellFamilyAttachment.collarRetraction ι n (controlledPoint ι n z) = direction ι n z := by
  apply (CellFamilyAttachment.boundaryToDisks_isClosedEmbedding ι n).injective
  exact ((CellFamilyAttachment.ndrData ι n).map_retraction (controlledPoint ι n z)).trans
    (ndrEndpoint_direction n z)

variable (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The actual characteristic map of the annular points into the actual open outer region. -/
def toOuter : C(CellCollarCover.annulus ι n, CellCollarCover.U X n a) :=
  (CellCollarDeformation.collarMap X n a).hom.comp (controlledPoint ι n)

/-- Its underlying point is the original characteristic map of the same annular disk point. -/
theorem toOuter_val (z : CellCollarCover.annulus ι n) :
    (toOuter X n a z).1 = CellFamilyAttachment.diskInclusion X n a z.1 :=
  rfl

/-- Following the actual annular characteristic by the original-space retraction
is the original attaching map of the normalized boundary direction. -/
theorem retraction_toOuter (z : CellCollarCover.annulus ι n) :
    CellCollarDeformation.retractionU X n a (toOuter X n a z) =
      CellFamilyAttachment.attachingMap X n a (direction ι n z) := by
  have h := ConcreteCategory.congr_hom
    (CellCollarDeformation.collarMap_retractionU X n a) (controlledPoint ι n z)
  change CellCollarDeformation.retractionU X n a (toOuter X n a z) =
    CellFamilyAttachment.attachingMap X n a
      (CellFamilyAttachment.collarRetraction ι n (controlledPoint ι n z)) at h
  exact h.trans (congrArg (CellFamilyAttachment.attachingMap X n a)
    (controlledRetraction_direction n z))

end AlgebraicTopology.CellAnnulusDeformation

end

end
