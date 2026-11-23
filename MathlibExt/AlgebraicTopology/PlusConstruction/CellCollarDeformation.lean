/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarCover
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyNDR
public import MathlibExt.Topology.Category.TopPair.NDRPushout
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Deformation of the actual outer cell-attachment region

The original disk-family NDR data descends to the actual cell-attachment
pushout. Its controlled neighborhood is the previously constructed open
region `U`, the complement of the image of the closed half-radius cores.
Restricting the descended deformation constructs a strong deformation of
`U` onto the original space, with the original inclusion and retraction.

On each original disk collar, the retraction is the original radial boundary
retraction followed by the original attaching map. These characteristics
retain the maps needed for the subsequent annular van Kampen comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.CellCollarDeformation

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The pair formed by the actual original-space cell-attachment inclusion. -/
def attachmentPair : TopPair.{u} :=
  TopPair.NDRPushout.pair (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n)

theorem attachmentPair_fst :
    (attachmentPair X n a).fst = CellFamilyAttachment.space X n a :=
  rfl

theorem attachmentPair_snd : (attachmentPair X n a).snd = X :=
  rfl

theorem attachmentPair_map :
    (attachmentPair X n a).map = CellFamilyAttachment.inclusion X n a :=
  rfl

/-- Controlled data constructed on the actual attachment, from its original disk family. -/
def attachmentData : TopPair.NDRData (attachmentPair X n a) :=
  TopPair.NDRPushout.data (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n)

theorem attachmentData_control_inclusion (x : X) :
    (attachmentData X n a).control (CellFamilyAttachment.inclusion X n a x) = 0 :=
  TopPair.NDRPushout.control_inclusion (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n) x

theorem attachmentData_control_disk (b : CellFamilyAttachment.disks ι n) :
    (attachmentData X n a).control (CellFamilyAttachment.diskInclusion X n a b) =
      (CellFamilyAttachment.ndrData ι n).control b :=
  TopPair.NDRPushout.control_left (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n) b

/-- The actual attachment control has the original clamped norm formula on every disk. -/
theorem attachmentData_control_cell (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    (attachmentData X n a).control (CellFamilyAttachment.cell X n a i z) =
      Set.projIcc 0 1 zero_le_one (2 * (1 - ‖z.down.val‖)) := by
  have h := attachmentData_control_disk X n a (⟨i, z⟩ : CellFamilyAttachment.disks ι n)
  change (attachmentData X n a).control (CellFamilyAttachment.cell X n a i z) =
    (CellFamilyAttachment.ndrData ι n).control ⟨i, z⟩ at h
  exact h.trans (CellFamilyAttachment.ndrData_control_apply n i z)

theorem attachmentData_endpoint_inclusion (x : X) :
    (attachmentData X n a).endpoint (CellFamilyAttachment.inclusion X n a x) =
      CellFamilyAttachment.inclusion X n a x :=
  TopPair.NDRPushout.endpoint_inclusion (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n) x

theorem attachmentData_endpoint_disk (b : CellFamilyAttachment.disks ι n) :
    (attachmentData X n a).endpoint (CellFamilyAttachment.diskInclusion X n a b) =
      CellFamilyAttachment.diskInclusion X n a ((CellFamilyAttachment.ndrData ι n).endpoint b) :=
  TopPair.NDRPushout.endpoint_left (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n) b

theorem attachmentData_deformation_inclusion (t : I) (x : X) :
    (attachmentData X n a).deformation (t, CellFamilyAttachment.inclusion X n a x) =
      CellFamilyAttachment.inclusion X n a x :=
  TopPair.NDRPushout.deformation_inclusion (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n) t x

theorem attachmentData_deformation_disk (t : I) (b : CellFamilyAttachment.disks ι n) :
    (attachmentData X n a).deformation (t, CellFamilyAttachment.diskInclusion X n a b) =
      CellFamilyAttachment.diskInclusion X n a
        ((CellFamilyAttachment.ndrData ι n).deformation (t, b)) :=
  TopPair.NDRPushout.deformation_left (CellFamilyAttachment.literalPair ι n)
    (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n) t b

/-- The controlled neighborhood is the actual open outer region of the attachment. -/
theorem attachmentData_neighborhood :
    (attachmentData X n a).neighborhood = CellCollarCover.U X n a := by
  have h : (attachmentData X n a).neighborhood =
      Set.range (CellFamilyAttachment.inclusion X n a) ∪
        CellFamilyAttachment.diskInclusion X n a ''
          (CellFamilyAttachment.ndrData ι n).neighborhood :=
    TopPair.NDRPushout.neighborhood_eq_range_union_image
      (CellFamilyAttachment.literalPair ι n)
      (CellFamilyAttachment.attachingMap X n a) (CellFamilyAttachment.ndrData ι n)
  have hCollar : (CellFamilyAttachment.ndrData ι n).neighborhood =
      CellCollarCover.collar ι n :=
    CellFamilyAttachment.ndrData_neighborhood ι n
  rw [hCollar] at h
  exact h.trans (CellCollarCover.U_eq_range_inclusion_union_image_collar X n a).symm

/-- The constructed global deformation preserves the actual open outer region. -/
theorem deformation_mem_U (t : I) (y : CellFamilyAttachment.space X n a)
    (hy : y ∈ CellCollarCover.U X n a) :
    (attachmentData X n a).deformation (t, y) ∈ CellCollarCover.U X n a := by
  rw [← attachmentData_neighborhood X n a] at hy ⊢
  exact (attachmentData X n a).deformation_mem_neighborhood t hy

/-- Every original-space point lies in the actual outer region. -/
theorem inclusion_mem_U (x : X) :
    CellFamilyAttachment.inclusion X n a x ∈ CellCollarCover.U X n a := by
  have hx : x ∈ CellFamilyAttachment.inclusion X n a ⁻¹' CellCollarCover.U X n a := by
    simpa only [CellCollarCover.inclusion_preimage_U] using (Set.mem_univ x)
  exact hx

/-- The actual outer region, viewed as the equal constructed controlled neighborhood. -/
def toControlledNeighborhood :
    TopCat.of (CellCollarCover.U X n a) ⟶ TopCat.of (attachmentData X n a).neighborhood :=
  TopCat.ofHom
    { toFun := fun z : CellCollarCover.U X n a =>
        Homeomorph.setCongr (attachmentData_neighborhood X n a).symm z
      continuous_toFun := by
        exact (Homeomorph.setCongr (attachmentData_neighborhood X n a).symm).continuous }

/-- The original inclusion with codomain restricted to the actual open outer region. -/
def inclusionU : X ⟶ TopCat.of (CellCollarCover.U X n a) :=
  TopCat.ofHom
    { toFun := fun x => ⟨CellFamilyAttachment.inclusion X n a x, by
        exact inclusion_mem_U X n a x⟩
      continuous_toFun := by
        exact (CellFamilyAttachment.inclusion X n a).hom.continuous.subtype_mk
          (fun x => by exact inclusion_mem_U X n a x) }

theorem inclusionU_val (x : X) :
    (inclusionU X n a x).1 = CellFamilyAttachment.inclusion X n a x :=
  rfl

/-- The constructed retraction of the actual open outer region onto the original space. -/
def retractionU : TopCat.of (CellCollarCover.U X n a) ⟶ X :=
  toControlledNeighborhood X n a ≫ (attachmentData X n a).retraction

/-- The original inclusion after the actual retraction is the constructed radial endpoint. -/
theorem inclusion_retractionU (z : CellCollarCover.U X n a) :
    CellFamilyAttachment.inclusion X n a (retractionU X n a z) =
      (attachmentData X n a).endpoint z.1 := by
  have hRet : retractionU X n a z =
      (attachmentData X n a).retraction (toControlledNeighborhood X n a z) :=
    TopCat.comp_app (toControlledNeighborhood X n a) (attachmentData X n a).retraction z
  have hVal : (toControlledNeighborhood X n a z).1 = z.1 := rfl
  have h := (attachmentData X n a).map_retraction (toControlledNeighborhood X n a z)
  rw [attachmentPair_map X n a] at h
  have hEndpoint :
      CellFamilyAttachment.inclusion X n a
          ((attachmentData X n a).retraction (toControlledNeighborhood X n a z)) =
        (attachmentData X n a).endpoint z.1 :=
    Eq.trans (α := CellFamilyAttachment.space X n a)
      (b := (attachmentData X n a).endpoint (toControlledNeighborhood X n a z).1)
      h (congrArg (attachmentData X n a).endpoint hVal)
  exact Eq.trans (α := CellFamilyAttachment.space X n a)
    (b := CellFamilyAttachment.inclusion X n a
      ((attachmentData X n a).retraction (toControlledNeighborhood X n a z)))
    (congrArg (CellFamilyAttachment.inclusion X n a) hRet) hEndpoint

/-- The actual outer-region retraction is the identity after the original inclusion. -/
@[reassoc]
theorem inclusionU_retractionU : inclusionU X n a ≫ retractionU X n a = 𝟙 X := by
  apply TopCat.ext
  intro x
  apply (CellFamilyAttachment.inclusion_injective X n a)
  have h := inclusion_retractionU X n a (inclusionU X n a x)
  change CellFamilyAttachment.inclusion X n a (retractionU X n a (inclusionU X n a x)) =
    (attachmentData X n a).endpoint (CellFamilyAttachment.inclusion X n a x) at h
  exact h.trans (attachmentData_endpoint_inclusion X n a x)

/-- The actual outer region deforms to inclusion after retraction, fixing the original space. -/
def deformationU :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (CellCollarCover.U X n a))
      (retractionU X n a ≫ inclusionU X n a).hom
      (Set.range (inclusionU X n a)) where
  toFun p := ⟨(attachmentData X n a).deformation (p.1, p.2.1), by
    exact deformation_mem_U X n a p.1 p.2.1 p.2.2⟩
  continuous_toFun := by
    have hval : Continuous (fun z : CellCollarCover.U X n a =>
        (z.1 : CellFamilyAttachment.space X n a)) :=
      continuous_subtype_val
    have hpair : Continuous (fun p : I × CellCollarCover.U X n a =>
        (p.1, (p.2.1 : CellFamilyAttachment.space X n a))) :=
      continuous_fst.prodMk (hval.comp continuous_snd)
    exact ((attachmentData X n a).deformation.continuous.comp hpair).subtype_mk
        (fun p => by exact deformation_mem_U X n a p.1 p.2.1 p.2.2)
  map_zero_left z := by
    apply Subtype.ext
    exact (attachmentData X n a).deformation.apply_zero z.1
  map_one_left z := by
    apply Subtype.ext
    exact ((attachmentData X n a).deformation.apply_one z.1).trans
      (inclusion_retractionU X n a z).symm
  prop' t z hz := by
    rcases hz with ⟨x, rfl⟩
    apply Subtype.ext
    exact attachmentData_deformation_inclusion X n a t x

theorem deformationU_val (t : I) (z : CellCollarCover.U X n a) :
    (deformationU X n a (t, z)).1 = (attachmentData X n a).deformation (t, z.1) :=
  rfl

theorem deformationU_inclusion (t : I) (x : X) :
    deformationU X n a (t, inclusionU X n a x) = inclusionU X n a x :=
  (deformationU X n a).eq_fst t ⟨x, rfl⟩

/-- The original space and actual open outer region are homotopy equivalent by these maps. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv X (CellCollarCover.U X n a) where
  toFun := (inclusionU X n a).hom
  invFun := (retractionU X n a).hom
  left_inv := by
    have h : (retractionU X n a).hom.comp (inclusionU X n a).hom =
        ContinuousMap.id X := by
      apply ContinuousMap.ext
      intro x
      exact ConcreteCategory.congr_hom (inclusionU_retractionU X n a) x
    exact ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id X)).cast h.symm rfl⟩
  right_inv := by
    exact ⟨(deformationU X n a).toHomotopy.symm⟩

theorem homotopyEquiv_toFun :
    (homotopyEquiv X n a).toFun = (inclusionU X n a).hom :=
  rfl

theorem homotopyEquiv_invFun :
    (homotopyEquiv X n a).invFun = (retractionU X n a).hom :=
  rfl

/-- An original disk-collar point maps into the actual open outer region. -/
theorem diskCollar_mem_U (z : (CellFamilyAttachment.ndrData ι n).neighborhood) :
    CellFamilyAttachment.diskInclusion X n a z.1 ∈ CellCollarCover.U X n a := by
  rw [← attachmentData_neighborhood X n a]
  apply ((attachmentData X n a).mem_neighborhood _).mpr
  rw [attachmentData_control_disk X n a z.1]
  exact ((CellFamilyAttachment.ndrData ι n).mem_neighborhood z.1).mp z.2

/-- The original family collars included in the actual outer region by the characteristic map. -/
def collarMap :
    TopCat.of (CellFamilyAttachment.ndrData ι n).neighborhood ⟶
      TopCat.of (CellCollarCover.U X n a) :=
  TopCat.ofHom
    { toFun := fun z => ⟨CellFamilyAttachment.diskInclusion X n a z.1, by
        exact diskCollar_mem_U X n a z⟩
      continuous_toFun := by
        exact ((CellFamilyAttachment.diskInclusion X n a).hom.continuous.comp
          continuous_subtype_val).subtype_mk (fun z => by exact diskCollar_mem_U X n a z) }

/-- On original disk collars, the actual retraction is the original attaching map
after the original radial boundary retraction. -/
@[reassoc]
theorem collarMap_retractionU :
    collarMap X n a ≫ retractionU X n a =
      CellFamilyAttachment.collarRetraction ι n ≫ CellFamilyAttachment.attachingMap X n a := by
  apply TopCat.ext
  intro z
  apply CellFamilyAttachment.inclusion_injective X n a
  have hRet := inclusion_retractionU X n a (collarMap X n a z)
  have hEnd := attachmentData_endpoint_disk X n a z.1
  have hBoundary := (CellFamilyAttachment.ndrData ι n).map_retraction z
  have hGlue := ConcreteCategory.congr_hom (CellFamilyAttachment.isPushout X n a).w
    (CellFamilyAttachment.collarRetraction ι n z)
  change CellFamilyAttachment.diskInclusion X n a
      (CellFamilyAttachment.boundaryToDisks ι n (CellFamilyAttachment.collarRetraction ι n z)) =
    CellFamilyAttachment.inclusion X n a
      (CellFamilyAttachment.attachingMap X n a (CellFamilyAttachment.collarRetraction ι n z))
        at hGlue
  exact hRet.trans (hEnd.trans
    ((congrArg (CellFamilyAttachment.diskInclusion X n a) hBoundary.symm).trans hGlue))

/-- The actual outer-region deformation retains the original family radial deformation. -/
theorem deformationU_collarMap (t : I)
    (z : (CellFamilyAttachment.ndrData ι n).neighborhood) :
    (deformationU X n a (t, collarMap X n a z)).1 =
      CellFamilyAttachment.diskInclusion X n a
        ((CellFamilyAttachment.ndrData ι n).deformation (t, z.1)) := by
  exact attachmentData_deformation_disk X n a t z.1

end AlgebraicTopology.CellCollarDeformation

end

end
