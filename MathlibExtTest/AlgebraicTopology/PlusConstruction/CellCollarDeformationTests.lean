/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarDeformation
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Ordinary clients for the actual cell collar deformation

Generic consumers retain arbitrary carrier universes, positive cell dimensions
and original attaching maps. No nonempty source or cell index is assumed.
The universe-one empty family checks the actual regions and inverse maps.
Two universe-one cells have different attaching maps depending on an original
boundary coordinate. A literal annulus vector with distinct nonzero coordinates
checks the norm control, retraction values and radial deformation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.CellCollarDeformationTests

/-- An interior time, used rather than a homotopy endpoint. -/
def interiorTime : I := ⟨1 / 2, by norm_num⟩

section Generic

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The original inclusion and actual collar retraction compose to identity without
any nonempty-source or nonempty-index hypothesis. -/
theorem genericRetractionClient :
    CellCollarDeformation.inclusionU X n a ≫ CellCollarDeformation.retractionU X n a = 𝟙 X :=
  CellCollarDeformation.inclusionU_retractionU X n a

/-- Every original-source point is fixed at a genuine interior time in every universe. -/
theorem genericSourceInteriorClient (x : X) :
    CellCollarDeformation.deformationU X n a
        (interiorTime, CellCollarDeformation.inclusionU X n a x) =
      CellCollarDeformation.inclusionU X n a x :=
  CellCollarDeformation.deformationU_inclusion X n a interiorTime x

/-- The three actual region preimages on the original source need no nonemptiness assumptions. -/
theorem genericOriginalPreimagesClient :
    CellFamilyAttachment.inclusion X n a ⁻¹' CellCollarCover.U X n a = Set.univ ∧
    CellFamilyAttachment.inclusion X n a ⁻¹' CellCollarCover.V X n a = ∅ ∧
    CellFamilyAttachment.inclusion X n a ⁻¹'
        (CellCollarCover.U X n a ∩ CellCollarCover.V X n a) = ∅ :=
  ⟨CellCollarCover.inclusion_preimage_U X n a,
    CellCollarCover.inclusion_preimage_V X n a,
    CellCollarCover.inclusion_preimage_intersection X n a⟩

/-- The actual component collar retraction is followed by that same original
component's attaching map. -/
theorem genericCollarCharacteristicClient (i : ι) :
    CellFamilyAttachment.collarι n i ≫ CellCollarDeformation.collarMap X n a ≫
        CellCollarDeformation.retractionU X n a =
      (classicalCellDiskPairNDRData.{u} (n + 1)).retraction ≫ a i := by
  have hBoundary :
      TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i ≫
          CellFamilyAttachment.attachingMap X n a = a i :=
    CellFamilyAttachment.boundaryι_desc n a i
  calc
    CellFamilyAttachment.collarι n i ≫
        (CellCollarDeformation.collarMap X n a ≫ CellCollarDeformation.retractionU X n a) =
        CellFamilyAttachment.collarι n i ≫
          (CellFamilyAttachment.collarRetraction ι n ≫
            CellFamilyAttachment.attachingMap X n a) :=
      congrArg (fun f : TopCat.of (CellFamilyAttachment.ndrData ι n).neighborhood ⟶ X =>
        CellFamilyAttachment.collarι n i ≫ f)
          (CellCollarDeformation.collarMap_retractionU X n a)
    _ = (CellFamilyAttachment.collarι n i ≫ CellFamilyAttachment.collarRetraction ι n) ≫
        CellFamilyAttachment.attachingMap X n a :=
      (Category.assoc _ _ _).symm
    _ = ((classicalCellDiskPairNDRData.{u} (n + 1)).retraction ≫
          TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i) ≫
        CellFamilyAttachment.attachingMap X n a :=
      congrArg (fun f : TopCat.of (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood ⟶
          CellFamilyAttachment.boundaries ι n => f ≫ CellFamilyAttachment.attachingMap X n a)
        (CellFamilyAttachment.collarRetraction_component n i)
    _ = (classicalCellDiskPairNDRData.{u} (n + 1)).retraction ≫
        (TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i ≫
          CellFamilyAttachment.attachingMap X n a) :=
      Category.assoc _ _ _
    _ = (classicalCellDiskPairNDRData.{u} (n + 1)).retraction ≫ a i :=
      congrArg (fun f : (classicalCellDiskPair.{u} (n + 1)).snd ⟶ X =>
        (classicalCellDiskPairNDRData.{u} (n + 1)).retraction ≫ f) hBoundary

end Generic

/-- The original source has actual carrier universe one. -/
def sourceSpace : TopCat.{1} := TopCat.of (ULift.{1} ℝ)

/-- The two-cell index itself has carrier universe one. -/
abbrev TwoCellIndex := ULift.{1} (Fin 2)

/-- The two original attaching values have distinct offsets. -/
def offset (i : TwoCellIndex) : ℝ := if i.down = 0 then 3 else 7

/-- The original boundary coordinate matters as well as the actual cell index. -/
def attachingMaps (i : TwoCellIndex) :
    ((classicalCellDiskPair.{1} 2).snd ⟶ sourceSpace) :=
  TopCat.ofHom
    { toFun := fun b => ULift.up (offset i + b.down.val (0 : Fin 2))
      continuous_toFun := by
        exact continuous_uliftUp.comp
          (continuous_const.add ((continuous_apply (0 : Fin 2)).comp
            (continuous_subtype_val.comp continuous_uliftDown))) }

/-- The actual two-cell attachment of the original lifted real line. -/
def twoSpace : TopCat.{1} := CellFamilyAttachment.space sourceSpace 1 attachingMaps

/-- The actual outer region of this attachment. -/
def twoOuter : Set twoSpace := CellCollarCover.U sourceSpace 1 attachingMaps

/-- The actual inner region of this attachment. -/
def twoInner : Set twoSpace := CellCollarCover.V sourceSpace 1 attachingMaps

private theorem vector_mem_closedBall (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (![x, y] : Fin 2 → ℝ) ∈ Metric.closedBall 0 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  fin_cases j
  · change ‖x‖ ≤ 1
    exact (Real.norm_eq_abs x).trans_le hx
  · change ‖y‖ ≤ 1
    exact (Real.norm_eq_abs y).trans_le hy

/-- A literal disk point of max norm five eighths, with unequal nonzero coordinates. -/
def annulusPoint : (classicalCellDiskPair.{1} 2).fst :=
  ULift.up ⟨![3 / 8, 5 / 8], by
    exact vector_mem_closedBall _ _ (by norm_num) (by norm_num)⟩

/-- The actual center of the original disk is a core point. -/
def centerPoint : (classicalCellDiskPair.{1} 2).fst :=
  ULift.up ⟨(0 : Fin 2 → ℝ), by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_zero] using
      (zero_le_one : (0 : ℝ) ≤ 1)⟩

/-- The expected nontrivial radial image at half time, still in the original disk. -/
def radialHalfPoint : (classicalCellDiskPair.{1} 2).fst :=
  ULift.up ⟨![39 / 80, 13 / 16], by
    exact vector_mem_closedBall _ _ (by norm_num) (by norm_num)⟩

/-- The original annulus point has exactly the specified max norm. -/
theorem annulusPoint_norm : ‖annulusPoint.down.val‖ = (5 : ℝ) / 8 := by
  have hle : ‖(![3 / 8, 5 / 8] : Fin 2 → ℝ)‖ ≤ (5 : ℝ) / 8 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8)).mpr
    intro j
    fin_cases j
    · change ‖(3 / 8 : ℝ)‖ ≤ 5 / 8
      norm_num
    · change ‖(5 / 8 : ℝ)‖ ≤ 5 / 8
      norm_num
  have hge : (5 : ℝ) / 8 ≤ ‖(![3 / 8, 5 / 8] : Fin 2 → ℝ)‖ := by
    have h := norm_le_pi_norm (![3 / 8, 5 / 8] : Fin 2 → ℝ) (1 : Fin 2)
    change ‖(5 / 8 : ℝ)‖ ≤ ‖(![3 / 8, 5 / 8] : Fin 2 → ℝ)‖ at h
    have heq : ‖(5 / 8 : ℝ)‖ = (5 : ℝ) / 8 := by norm_num
    simpa only [heq] using h
  exact le_antisymm hle hge

/-- The original center has norm zero. -/
theorem centerPoint_norm : ‖centerPoint.down.val‖ = 0 :=
  norm_zero

/-- The original annulus radial scale is exactly eight fifths. -/
theorem annulusPoint_scale :
    TopPair.closedUnitBallRadialScale annulusPoint.down.val = (8 : ℝ) / 5 := by
  change (max ‖annulusPoint.down.val‖ ((1 : ℝ) / 2))⁻¹ = (8 : ℝ) / 5
  exact (congrArg (fun r : ℝ => r⁻¹)
    ((congrArg (fun r : ℝ => max r ((1 : ℝ) / 2)) annulusPoint_norm).trans
      (max_eq_left (by norm_num : (1 : ℝ) / 2 ≤ 5 / 8)))).trans (by norm_num)

/-- The original annulus point in the actual component controlled neighborhood. -/
def componentCollar : (classicalCellDiskPairNDRData.{1} 2).neighborhood :=
  ⟨annulusPoint, by
    have h : (CellFamilyAttachment.ndrData TwoCellIndex 1).control
        (⟨ULift.up (0 : Fin 2), annulusPoint⟩ : CellFamilyAttachment.disks TwoCellIndex 1) < 1 := by
      apply (CellFamilyAttachment.ndrData_control_lt_one_iff 1
        (⟨ULift.up (0 : Fin 2), annulusPoint⟩ :
          CellFamilyAttachment.disks TwoCellIndex 1)).mpr
      rw [annulusPoint_norm]
      norm_num
    rw [CellFamilyAttachment.ndrData_control_component] at h
    exact h⟩

/-- The same original collar point, retained in its actual indexed literal component. -/
def familyCollar (i : TwoCellIndex) : (CellFamilyAttachment.ndrData TwoCellIndex 1).neighborhood :=
  CellFamilyAttachment.collarι 1 i componentCollar

/-- The actual characteristic collar point in the constructed outer region. -/
def annulusInU (i : TwoCellIndex) : twoOuter :=
  CellCollarDeformation.collarMap sourceSpace 1 attachingMaps (familyCollar i)

/-- The actual radial boundary point returned by the original component retraction. -/
def normalizedBoundary : (classicalCellDiskPair.{1} 2).snd :=
  (classicalCellDiskPairNDRData.{1} 2).retraction componentCollar

/-- Retraction gives the original radial endpoint with coordinates three fifths and one. -/
theorem normalizedBoundary_coordinates : normalizedBoundary.down.val = ![3 / 5, 1] := by
  have h := congrArg (fun b : (classicalCellDiskPair.{1} 2).fst => b.down.val)
    ((classicalCellDiskPairNDRData.{1} 2).map_retraction componentCollar)
  change normalizedBoundary.down.val =
    (TopPair.closedUnitBallEndpoint (Fin 2 → ℝ) annulusPoint).down.val at h
  have he := TopPair.closedUnitBallEndpoint_down_val (E := Fin 2 → ℝ) annulusPoint
  have hv : (8 / 5 : ℝ) • annulusPoint.down.val = (![3 / 5, 1] : Fin 2 → ℝ) := by
    funext j
    fin_cases j
    · change (8 / 5 : ℝ) * (3 / 8) = 3 / 5
      norm_num
    · change (8 / 5 : ℝ) * (5 / 8) = 1
      norm_num
  exact h.trans (he.trans
    ((congrArg (fun r : ℝ => r • annulusPoint.down.val) annulusPoint_scale).trans hv))

/-- The exact outer, inner and overlap preimages retain the original literal disk points. -/
theorem finitePreimagesClient :
    CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps ⁻¹' twoOuter =
        {z : CellFamilyAttachment.disks TwoCellIndex 1 | (1 : ℝ) / 2 < ‖z.2.down.val‖} ∧
    CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps ⁻¹' twoInner =
        {z : CellFamilyAttachment.disks TwoCellIndex 1 | ‖z.2.down.val‖ < (3 : ℝ) / 4} ∧
    CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps ⁻¹' (twoOuter ∩ twoInner) =
        {z : CellFamilyAttachment.disks TwoCellIndex 1 |
          (1 : ℝ) / 2 < ‖z.2.down.val‖ ∧ ‖z.2.down.val‖ < (3 : ℝ) / 4} :=
  ⟨CellCollarCover.diskInclusion_preimage_U_collar sourceSpace 1 attachingMaps,
    CellCollarCover.diskInclusion_preimage_V sourceSpace 1 attachingMaps,
    CellCollarCover.diskInclusion_preimage_intersection sourceSpace 1 attachingMaps⟩

/-- Each actual annulus point belongs to both regions; each center belongs only to the inner one. -/
theorem annulusAndCoreClient (i : TwoCellIndex) :
    CellFamilyAttachment.cell sourceSpace 1 attachingMaps i annulusPoint ∈ twoOuter ∩ twoInner ∧
    CellFamilyAttachment.cell sourceSpace 1 attachingMaps i centerPoint ∈ twoInner ∧
    CellFamilyAttachment.cell sourceSpace 1 attachingMaps i centerPoint ∉ twoOuter := by
  have hAnn : (⟨i, annulusPoint⟩ : CellFamilyAttachment.disks TwoCellIndex 1) ∈
      CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps ⁻¹'
        (twoOuter ∩ twoInner) := by
    rw [finitePreimagesClient.2.2]
    change (1 : ℝ) / 2 < ‖annulusPoint.down.val‖ ∧
      ‖annulusPoint.down.val‖ < (3 : ℝ) / 4
    rw [annulusPoint_norm]
    constructor <;> norm_num
  have hCenter : (⟨i, centerPoint⟩ : CellFamilyAttachment.disks TwoCellIndex 1) ∈
      CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps ⁻¹' twoInner := by
    rw [finitePreimagesClient.2.1]
    change ‖centerPoint.down.val‖ < (3 : ℝ) / 4
    rw [centerPoint_norm]
    norm_num
  refine ⟨hAnn, hCenter, ?_⟩
  intro h
  have hb : (⟨i, centerPoint⟩ : CellFamilyAttachment.disks TwoCellIndex 1) ∈
      CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps ⁻¹' twoOuter := h
  rw [finitePreimagesClient.1] at hb
  change (1 : ℝ) / 2 < ‖centerPoint.down.val‖ at hb
  rw [centerPoint_norm] at hb
  norm_num at hb

/-- The actual original clamped NDR control distinguishes the annulus from the center. -/
theorem finiteControlClient (i : TwoCellIndex) :
    ((CellCollarDeformation.attachmentData sourceSpace 1 attachingMaps).control
        (CellFamilyAttachment.cell sourceSpace 1 attachingMaps i annulusPoint) : ℝ) =
        (3 : ℝ) / 4 ∧
    (CellCollarDeformation.attachmentData sourceSpace 1 attachingMaps).control
        (CellFamilyAttachment.cell sourceSpace 1 attachingMaps i centerPoint) = 1 := by
  constructor
  · have h := congrArg (fun t : I => (t : ℝ))
      (CellCollarDeformation.attachmentData_control_cell sourceSpace 1 attachingMaps i annulusPoint)
    have hc : (Set.projIcc 0 1 zero_le_one (2 * (1 - ‖annulusPoint.down.val‖)) : ℝ) =
        (3 : ℝ) / 4 := by
      rw [Set.coe_projIcc, annulusPoint_norm]
      norm_num
    exact h.trans hc
  · have h := CellCollarDeformation.attachmentData_control_cell
      sourceSpace 1 attachingMaps i centerPoint
    have hc : Set.projIcc 0 1 zero_le_one (2 * (1 - ‖centerPoint.down.val‖)) = (1 : I) := by
      apply Subtype.ext
      rw [Set.coe_projIcc, centerPoint_norm]
      norm_num
    exact h.trans hc

/-- The actual indexed retraction retains the original coordinate-dependent attaching value. -/
theorem annulusRetraction_value (i : TwoCellIndex) :
    CellCollarDeformation.retractionU sourceSpace 1 attachingMaps (annulusInU i) =
      ULift.up (offset i + (3 : ℝ) / 5) := by
  have h := ConcreteCategory.congr_hom
    (CellCollarDeformation.collarMap_retractionU sourceSpace 1 attachingMaps) (familyCollar i)
  have hr := ConcreteCategory.congr_hom
    (CellFamilyAttachment.collarRetraction_component 1 i) componentCollar
  change CellFamilyAttachment.collarRetraction TwoCellIndex 1 (familyCollar i) =
    (⟨i, normalizedBoundary⟩ : CellFamilyAttachment.boundaries TwoCellIndex 1) at hr
  change CellCollarDeformation.retractionU sourceSpace 1 attachingMaps (annulusInU i) =
    CellFamilyAttachment.attachingMap sourceSpace 1 attachingMaps
      (CellFamilyAttachment.collarRetraction TwoCellIndex 1 (familyCollar i)) at h
  rw [hr, CellFamilyAttachment.attachingMap_apply] at h
  have hv : attachingMaps i normalizedBoundary = ULift.up (offset i + (3 : ℝ) / 5) := by
    apply ULift.down_injective
    exact congrArg (fun v : Fin 2 → ℝ => offset i + v (0 : Fin 2))
      normalizedBoundary_coordinates
  exact h.trans hv

/-- The two actual attaching maps give distinct retraction values on their retained disk indices. -/
theorem finiteRetractionValuesClient :
    CellCollarDeformation.retractionU sourceSpace 1 attachingMaps
        (annulusInU (ULift.up (0 : Fin 2))) = ULift.up (18 / 5 : ℝ) ∧
    CellCollarDeformation.retractionU sourceSpace 1 attachingMaps
        (annulusInU (ULift.up (1 : Fin 2))) = ULift.up (38 / 5 : ℝ) := by
  constructor
  · have h := annulusRetraction_value (ULift.up (0 : Fin 2))
    norm_num [offset] at h
    exact h
  · have h := annulusRetraction_value (ULift.up (1 : Fin 2))
    norm_num [offset] at h
    exact h

/-- At half time, the original radial deformation has the expected distinct vector coordinates. -/
theorem componentHalf_coordinates :
    (classicalCellDiskPairNDRData.{1} 2).deformation (interiorTime, annulusPoint) =
      radialHalfPoint := by
  apply ULift.down_injective
  apply Subtype.ext
  have h := TopPair.closedUnitBallDeformationMap_down_val
    (E := Fin 2 → ℝ) interiorTime annulusPoint
  have hf : TopPair.closedUnitBallRadialFactor interiorTime annulusPoint.down.val =
      (13 : ℝ) / 10 := by
    change (1 - (1 / 2 : ℝ)) + (1 / 2) *
      TopPair.closedUnitBallRadialScale annulusPoint.down.val = (13 : ℝ) / 10
    exact (congrArg (fun r : ℝ => (1 - (1 / 2 : ℝ)) + (1 / 2) * r)
      annulusPoint_scale).trans (by norm_num)
  have hv : (13 / 10 : ℝ) • annulusPoint.down.val =
      (![39 / 80, 13 / 16] : Fin 2 → ℝ) := by
    funext j
    fin_cases j
    · change (13 / 10 : ℝ) * (3 / 8) = 39 / 80
      norm_num
    · change (13 / 10 : ℝ) * (5 / 8) = 13 / 16
      norm_num
  exact h.trans ((congrArg (fun r : ℝ => r • annulusPoint.down.val) hf).trans hv)

/-- The actual outer-region homotopy preserves the index and performs the
nontrivial radial motion. -/
theorem finiteRadialDeformationClient (i : TwoCellIndex) :
    (CellCollarDeformation.deformationU sourceSpace 1 attachingMaps
        (interiorTime, annulusInU i)).1 =
      CellFamilyAttachment.cell sourceSpace 1 attachingMaps i radialHalfPoint := by
  have h := CellCollarDeformation.deformationU_collarMap
    sourceSpace 1 attachingMaps interiorTime (familyCollar i)
  change (CellCollarDeformation.deformationU sourceSpace 1 attachingMaps
      (interiorTime, annulusInU i)).1 =
    CellFamilyAttachment.diskInclusion sourceSpace 1 attachingMaps
      ((CellFamilyAttachment.ndrData TwoCellIndex 1).deformation
        (interiorTime, ⟨i, annulusPoint⟩)) at h
  rw [CellFamilyAttachment.ndrData_deformation_component, componentHalf_coordinates] at h
  exact h

/-- The empty cell index has actual carrier universe one. -/
abbrev EmptyCellIndex := ULift.{1} (Fin 0)

/-- The actual attaching family on the empty index, without a nonempty-index hypothesis. -/
def emptyMaps (i : EmptyCellIndex) : ((classicalCellDiskPair.{1} 2).snd ⟶ sourceSpace) :=
  Fin.elim0 i.down

/-- The computed empty-family attachment of the original space. -/
def emptySpace : TopCat.{1} := CellFamilyAttachment.space sourceSpace 1 emptyMaps

/-- The actual outer region of the empty-family attachment. -/
def emptyOuter : Set emptySpace := CellCollarCover.U sourceSpace 1 emptyMaps

/-- The actual inner region of the empty-family attachment. -/
def emptyInner : Set emptySpace := CellCollarCover.V sourceSpace 1 emptyMaps

/-- Every point of the actual empty-family pushout comes from the original source. -/
theorem emptyPoint_isOriginal (y : emptySpace) :
    ∃ x : sourceSpace, CellFamilyAttachment.inclusion sourceSpace 1 emptyMaps x = y := by
  rcases CellFamilyAttachment.exists_inclusion_or_cell sourceSpace 1 emptyMaps y with
    ⟨x, hx⟩ | ⟨i, _, _⟩
  · exact ⟨x, hx⟩
  · exact Fin.elim0 i.down

/-- For the genuine empty family, the outer region is the whole original-source image
and the inner region is empty. -/
theorem emptyRegionsClient :
    emptyOuter = Set.univ ∧ emptyInner = ∅ ∧
      emptyOuter = Set.range (CellFamilyAttachment.inclusion sourceSpace 1 emptyMaps) := by
  have hV : emptyInner = ∅ := by
    ext y
    constructor
    · intro hy
      change ∃ b ∈ CellCollarCover.inner EmptyCellIndex 1,
        CellFamilyAttachment.diskInclusion sourceSpace 1 emptyMaps b = y at hy
      obtain ⟨⟨i, _⟩, _, _⟩ := hy
      exact Fin.elim0 i.down
    · intro hy
      exact hy.elim
  have hU : emptyOuter = Set.univ := by
    have h := CellCollarCover.U_union_V sourceSpace 1 emptyMaps
    change emptyOuter ∪ emptyInner = Set.univ at h
    simpa only [hV, Set.union_empty] using h
  have hRange : Set.range (CellFamilyAttachment.inclusion sourceSpace 1 emptyMaps) =
      Set.univ := by
    ext y
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact emptyPoint_isOriginal y
  exact ⟨hU, hV, hU.trans hRange.symm⟩

/-- Every point of the empty outer region is an actual original-source section point. -/
theorem emptyPoint_isSection (z : emptyOuter) :
    ∃ x : sourceSpace, CellCollarDeformation.inclusionU sourceSpace 1 emptyMaps x = z := by
  obtain ⟨x, hx⟩ := emptyPoint_isOriginal z.1
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (CellCollarDeformation.inclusionU_val sourceSpace 1 emptyMaps x).trans hx

/-- The actual section and NDR retraction are inverse maps for the empty family. -/
theorem emptySectionInverseClient :
    CellCollarDeformation.inclusionU sourceSpace 1 emptyMaps ≫
        CellCollarDeformation.retractionU sourceSpace 1 emptyMaps = 𝟙 sourceSpace ∧
    CellCollarDeformation.retractionU sourceSpace 1 emptyMaps ≫
        CellCollarDeformation.inclusionU sourceSpace 1 emptyMaps = 𝟙 (TopCat.of emptyOuter) := by
  refine ⟨CellCollarDeformation.inclusionU_retractionU sourceSpace 1 emptyMaps, ?_⟩
  apply TopCat.ext
  intro z
  obtain ⟨x, rfl⟩ := emptyPoint_isSection z
  have h := ConcreteCategory.congr_hom
    (CellCollarDeformation.inclusionU_retractionU sourceSpace 1 emptyMaps) x
  exact congrArg
    (fun y : sourceSpace => CellCollarDeformation.inclusionU sourceSpace 1 emptyMaps y) h

/-- The actual empty-family outer-region homotopy is identity at the chosen interior time. -/
theorem emptyInteriorIdentityClient (z : emptyOuter) :
    CellCollarDeformation.deformationU sourceSpace 1 emptyMaps (interiorTime, z) = z := by
  obtain ⟨x, rfl⟩ := emptyPoint_isSection z
  exact CellCollarDeformation.deformationU_inclusion sourceSpace 1 emptyMaps interiorTime x

end AlgebraicTopology.CellCollarDeformationTests

end

end
