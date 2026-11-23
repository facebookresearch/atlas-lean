/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarDeformation
public import MathlibExt.Topology.Category.TopPair.ClosedBall.CollarNormalization

/-!
# Retraction preservation along the original cell collars

The existing radial deformation of each original classical disk preserves
its original boundary retraction. The component characteristics transfer
this equality to the literal indexed family and then to its actual image
in the open outer region `U` of the original cell attachment.

Every actual point of `U` is either an original-space point or the image of
an original disk collar. The existing deformation fixes the first kind,
and the collar equality handles the second. Thus the existing retraction
is constant along the existing deformation on every point of `U`.

All positive cell dimensions and arbitrary index types, including empty
families, are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.CellFamilyAttachment

variable {ι : Type u}

/-- Including a component's original restricted deformation gives the
original literal family deformation as an equality of collar points. -/
theorem collarDeformation_collarι (n : ℕ) (i : ι) (t : I)
    (z : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood) :
    collarDeformation ι n (t, collarι n i z) =
      collarι n i
        ((classicalCellDiskPairNDRData.{u} (n + 1)).neighborhoodDeformation (t, z)) := by
  apply Subtype.ext
  change (collarDeformation ι n (t, collarι n i z)).1 =
    (⟨i, ((classicalCellDiskPairNDRData.{u} (n + 1)).neighborhoodDeformation
      (t, z)).1⟩ : disks ι n)
  rw [collarDeformation_val, collarι_val]
  exact ndrData_deformation_component n i t z.1

/-- The original literal retraction is constant on each component's
original restricted radial deformation. -/
theorem collarRetraction_collarDeformation_component (n : ℕ) (i : ι) (t : I)
    (z : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood) :
    collarRetraction ι n (collarDeformation ι n (t, collarι n i z)) =
      collarRetraction ι n (collarι n i z) := by
  have hLocal :
      (classicalCellDiskPairNDRData.{u} (n + 1)).retraction
          ((classicalCellDiskPairNDRData.{u} (n + 1)).neighborhoodDeformation (t, z)) =
        (classicalCellDiskPairNDRData.{u} (n + 1)).retraction z :=
    TopPair.closedUnitBallNeighborhoodDeformation_retraction.{u} (Fin (n + 1) → ℝ) t z
  let j : (classicalCellDiskPair.{u} (n + 1)).snd → boundaries ι n :=
    fun b => TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i b
  have hComponent (w : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood) :
      collarRetraction ι n (collarι n i w) =
        j ((classicalCellDiskPairNDRData.{u} (n + 1)).retraction w) :=
    ConcreteCategory.congr_hom (collarRetraction_component n i) w
  have hDeformation : collarDeformation ι n (t, collarι n i z) =
      collarι n i
        ((classicalCellDiskPairNDRData.{u} (n + 1)).neighborhoodDeformation (t, z)) :=
    collarDeformation_collarι n i t z
  exact (congrArg (collarRetraction ι n) hDeformation).trans
    ((hComponent
      ((classicalCellDiskPairNDRData.{u} (n + 1)).neighborhoodDeformation (t, z))).trans
        ((congrArg j hLocal).trans (hComponent z).symm))

/-- The existing boundary retraction is preserved by the existing
restricted NDR deformation on the whole original literal family collar. -/
theorem collarRetraction_collarDeformation (n : ℕ) (t : I)
    (z : (ndrData ι n).neighborhood) :
    collarRetraction ι n (collarDeformation ι n (t, z)) = collarRetraction ι n z := by
  rcases z with ⟨⟨i, b⟩, hb⟩
  have hLocal : (classicalCellDiskPairNDRData.{u} (n + 1)).control b < 1 := by
    have h := (show (ndrData ι n).control ⟨i, b⟩ < 1 from hb)
    rw [ndrData_control_component] at h
    exact h
  let zLocal : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood := ⟨b, hLocal⟩
  have hz : collarι n i zLocal =
      (⟨⟨i, b⟩, hb⟩ : (ndrData ι n).neighborhood) := by
    apply Subtype.ext
    exact collarι_val n i zLocal
  rw [← hz]
  exact collarRetraction_collarDeformation_component n i t zLocal

end AlgebraicTopology.CellFamilyAttachment

namespace AlgebraicTopology.CellCollarDeformation

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The existing actual outer-region deformation on a collar image is
the image of the existing literal-family collar deformation. -/
theorem deformationU_collarMap_eq (t : I)
    (z : (CellFamilyAttachment.ndrData ι n).neighborhood) :
    deformationU X n a (t, collarMap X n a z) =
      collarMap X n a (CellFamilyAttachment.collarDeformation ι n (t, z)) := by
  apply Subtype.ext
  change (deformationU X n a (t, collarMap X n a z)).1 =
    CellFamilyAttachment.diskInclusion X n a
      (CellFamilyAttachment.collarDeformation ι n (t, z)).1
  exact (deformationU_collarMap X n a t z).trans
    (congrArg (CellFamilyAttachment.diskInclusion X n a)
      (CellFamilyAttachment.collarDeformation_val n t z)).symm

/-- The existing original-space retraction stays fixed on every original
collar image throughout the existing outer-region deformation. -/
theorem retractionU_deformationU_collarMap (t : I)
    (z : (CellFamilyAttachment.ndrData ι n).neighborhood) :
    retractionU X n a (deformationU X n a (t, collarMap X n a z)) =
      retractionU X n a (collarMap X n a z) := by
  have hRet (w : (CellFamilyAttachment.ndrData ι n).neighborhood) :
      retractionU X n a (collarMap X n a w) =
        CellFamilyAttachment.attachingMap X n a
          (CellFamilyAttachment.collarRetraction ι n w) :=
    ConcreteCategory.congr_hom (collarMap_retractionU X n a) w
  rw [deformationU_collarMap_eq]
  calc
    retractionU X n a
        (collarMap X n a (CellFamilyAttachment.collarDeformation ι n (t, z))) =
        CellFamilyAttachment.attachingMap X n a
          (CellFamilyAttachment.collarRetraction ι n
            (CellFamilyAttachment.collarDeformation ι n (t, z))) :=
      hRet _
    _ = CellFamilyAttachment.attachingMap X n a
        (CellFamilyAttachment.collarRetraction ι n z) :=
      congrArg (CellFamilyAttachment.attachingMap X n a)
        (CellFamilyAttachment.collarRetraction_collarDeformation n t z)
    _ = retractionU X n a (collarMap X n a z) :=
      (hRet z).symm

/-- The existing retraction is constant along the existing deformation of
every actual outer-region point of the original cell attachment. -/
theorem retractionU_deformationU (t : I) (z : CellCollarCover.U X n a) :
    retractionU X n a (deformationU X n a (t, z)) = retractionU X n a z := by
  have hz : z.1 ∈ Set.range (CellFamilyAttachment.inclusion X n a) ∪
      CellFamilyAttachment.diskInclusion X n a '' CellCollarCover.collar ι n := by
    rw [← CellCollarCover.U_eq_range_inclusion_union_image_collar X n a]
    exact z.2
  rcases hz with ⟨x, hx⟩ | ⟨b, hb, hby⟩
  · have hxU : inclusionU X n a x = z := by
      apply Subtype.ext
      exact hx
    calc
      retractionU X n a (deformationU X n a (t, z)) =
          retractionU X n a (deformationU X n a (t, inclusionU X n a x)) :=
        congrArg (fun w : CellCollarCover.U X n a =>
          retractionU X n a (deformationU X n a (t, w))) hxU.symm
      _ = retractionU X n a (inclusionU X n a x) :=
        congrArg (retractionU X n a) (deformationU_inclusion X n a t x)
      _ = retractionU X n a z := congrArg (retractionU X n a) hxU
  · have hbLocal : b ∈ (CellFamilyAttachment.ndrData ι n).neighborhood := by
      rw [CellFamilyAttachment.ndrData_neighborhood]
      exact hb
    let bLocal : (CellFamilyAttachment.ndrData ι n).neighborhood := ⟨b, hbLocal⟩
    have hbU : collarMap X n a bLocal = z := by
      apply Subtype.ext
      exact hby
    calc
      retractionU X n a (deformationU X n a (t, z)) =
          retractionU X n a (deformationU X n a (t, collarMap X n a bLocal)) :=
        congrArg (fun w : CellCollarCover.U X n a =>
          retractionU X n a (deformationU X n a (t, w))) hbU.symm
      _ = retractionU X n a (collarMap X n a bLocal) :=
        retractionU_deformationU_collarMap X n a t bLocal
      _ = retractionU X n a z := congrArg (retractionU X n a) hbU

end AlgebraicTopology.CellCollarDeformation

end

end
