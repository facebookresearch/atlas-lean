/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellAttachment

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Ordinary clients for actual loop-cell attachments

The lifted real line carries a nonconstant arch loop. Its peak distinguishes
the traced square edge from the three constant edges. Two actual cells use
this loop and its reverse; an empty family recovers the original space by
the universal descent map. Generic universe-one subgroup clients use the
original path classes, based fundamental-group map and quotient factorization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex
open scoped unitInterval

namespace AlgebraicTopology.LoopCellAttachmentTests

/-- The actual target has carrier universe one. -/
def archSpace : TopCat.{1} := TopCat.of (ULift.{1} ℝ)

/-- The original basepoint on the lifted real line. -/
def archBasepoint : archSpace := ULift.up 0

/-- The peak parameter one-third in the original path interval. -/
def archPeakParameter : I := ⟨1 / 3, by norm_num⟩

/-- A nonconstant based loop whose real coordinate is 27t(1-t)^2/4. -/
def archLoop : Path archBasepoint archBasepoint where
  toFun t := ULift.up ((27 / 4) * (t : ℝ) * (1 - (t : ℝ)) ^ 2)
  continuous_toFun := by
    exact continuous_uliftUp.comp
      ((continuous_const.mul continuous_subtype_val).mul
        ((continuous_const.sub continuous_subtype_val).pow 2))
  source' := by
    apply ULift.down_injective
    norm_num [archBasepoint]
  target' := by
    apply ULift.down_injective
    norm_num [archBasepoint]

/-- The actual loop attains its maximum value one at one-third. -/
theorem archPeakClient :
    archLoop archPeakParameter = ULift.up (1 : ℝ) ∧ ∀ t : I, (archLoop t).down ≤ 1 := by
  constructor
  · apply ULift.down_injective
    change (27 / 4 : ℝ) * (1 / 3) * (1 - 1 / 3) ^ 2 = 1
    norm_num
  · intro t
    change (27 / 4) * (t : ℝ) * (1 - (t : ℝ)) ^ 2 ≤ 1
    have hlast : 0 ≤ (4 : ℝ) - 3 * (t : ℝ) := by
      linarith [unitInterval.le_one t]
    have hprod := mul_nonneg (sq_nonneg (3 * (t : ℝ) - 1)) hlast
    nlinarith [hprod]

/-- The concrete fixture is not the constant based path. -/
theorem archNonconstantClient : archLoop ≠ Path.refl archBasepoint := by
  intro h
  have hm := congrArg (fun p : Path archBasepoint archBasepoint => p archPeakParameter) h
  change archLoop archPeakParameter = archBasepoint at hm
  rw [archPeakClient.1] at hm
  have hd := congrArg ULift.down hm
  norm_num [archBasepoint] at hd

/-- At the chosen parameter on each edge, only the bottom trace reaches the peak. -/
theorem squareEdgeValuesClient :
    classicalCellSquareLoopMap archLoop (classicalCellSquareBottomPath.{1} archPeakParameter) =
        ULift.up (1 : ℝ) ∧
    classicalCellSquareLoopMap archLoop (classicalCellSquareRightPath.{1} archPeakParameter) =
        archBasepoint ∧
    classicalCellSquareLoopMap archLoop (classicalCellSquareTopPath.{1} archPeakParameter) =
        archBasepoint ∧
    classicalCellSquareLoopMap archLoop (classicalCellSquareLeftPath.{1} archPeakParameter) =
        archBasepoint := by
  have hb := congrArg (fun p : Path archBasepoint archBasepoint => p archPeakParameter)
    (classicalCellSquareLoopMap_bottomPath.{1, 1} archLoop)
  have hr := congrArg (fun p : Path archBasepoint archBasepoint => p archPeakParameter)
    (classicalCellSquareLoopMap_rightPath.{1, 1} archLoop)
  have ht := congrArg (fun p : Path archBasepoint archBasepoint => p archPeakParameter)
    (classicalCellSquareLoopMap_topPath.{1, 1} archLoop)
  have hl := congrArg (fun p : Path archBasepoint archBasepoint => p archPeakParameter)
    (classicalCellSquareLoopMap_leftPath.{1, 1} archLoop)
  change classicalCellSquareLoopMap archLoop
    (classicalCellSquareBottomPath.{1} archPeakParameter) = archLoop archPeakParameter at hb
  exact ⟨hb.trans archPeakClient.1, hr, ht, hl⟩

/-- The actual perimeter class uses both source and target universe one. -/
theorem perimeterClassClient :
    FundamentalGroup.mapOfEq (classicalCellSquareLoopMap archLoop)
        (classicalCellSquareLoopMap_bottomLeft archLoop)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{1})) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk archLoop) :=
  classicalCellSquareLoopMap_perimeter.{1, 1} archLoop

/-- The cell index itself has universe one. -/
abbrev TwoCellIndex := ULift.{1} (Fin 2)

/-- The two actual boundary maps trace the arch loop and its reverse. -/
def twoAttachingMaps (i : TwoCellIndex) : (classicalCellDiskPair.{1} 2).snd ⟶ archSpace :=
  TopCat.ofHom (classicalCellSquareLoopMap (if i.down = 0 then archLoop else archLoop.symm))

/-- The original computed attachment of those two disks. -/
def twoCellSpace : TopCat.{1} := CellFamilyAttachment.space archSpace 1 twoAttachingMaps

/-- The actual inclusion of the original lifted real line. -/
def twoCellInclusion : archSpace ⟶ twoCellSpace :=
  CellFamilyAttachment.inclusion archSpace 1 twoAttachingMaps

/-- The reversed-loop disk glues its bottom edge at one-third to the original
value one-half. -/
theorem twoCellGluingClient :
    twoCellInclusion (ULift.up (1 / 2 : ℝ)) =
      CellFamilyAttachment.cell archSpace 1 twoAttachingMaps (ULift.up (1 : Fin 2))
        ((classicalCellDiskPair.{1} 2).map
          (classicalCellSquareBottomPath.{1} archPeakParameter)) := by
  have hReversePeak : archLoop.symm archPeakParameter = ULift.up (1 / 2 : ℝ) := by
    apply ULift.down_injective
    change (27 / 4 : ℝ) * (1 - 1 / 3) * (1 - (1 - 1 / 3)) ^ 2 = 1 / 2
    norm_num
  have hp := congrArg (fun p : Path archBasepoint archBasepoint => p archPeakParameter)
    (classicalCellSquareLoopMap_bottomPath.{1, 1} archLoop.symm)
  change classicalCellSquareLoopMap archLoop.symm
    (classicalCellSquareBottomPath.{1} archPeakParameter) = archLoop.symm archPeakParameter at hp
  have hv : twoAttachingMaps (ULift.up (1 : Fin 2))
      (classicalCellSquareBottomPath.{1} archPeakParameter) = ULift.up (1 / 2 : ℝ) := by
    change classicalCellSquareLoopMap
      (if (1 : Fin 2) = 0 then archLoop else archLoop.symm)
      (classicalCellSquareBottomPath.{1} archPeakParameter) = ULift.up (1 / 2 : ℝ)
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    exact hp.trans hReversePeak
  have h := ConcreteCategory.congr_hom
    (CellFamilyAttachment.boundary_gluing archSpace 1 twoAttachingMaps
      (ULift.up (1 : Fin 2))) (classicalCellSquareBottomPath.{1} archPeakParameter)
  simp only [ConcreteCategory.comp_apply] at h
  rw [hv] at h
  exact h

/-- The two-cell space has the actual closed inclusion and both connectivity properties. -/
theorem twoCellPointSetClient :
    IsClosedEmbedding twoCellInclusion ∧ ConnectedSpace twoCellSpace ∧
      PathConnectedSpace twoCellSpace := by
  let : PathConnectedSpace archSpace :=
    (Homeomorph.ulift (X := ℝ)).symm.pathConnectedSpace
  exact ⟨CellFamilyAttachment.inclusion_isClosedEmbedding archSpace 1 twoAttachingMaps,
    CellFamilyAttachment.connectedSpace archSpace 1 twoAttachingMaps,
    CellFamilyAttachment.pathConnectedSpace archSpace 1 twoAttachingMaps⟩

/-- An actual empty family whose index still has universe one. -/
abbrev EmptyCellIndex := ULift.{1} (Fin 0)

/-- The unique boundary family on the actual empty index. -/
def emptyAttachingMaps (i : EmptyCellIndex) : (classicalCellDiskPair.{1} 2).snd ⟶ archSpace :=
  Fin.elim0 i.down

/-- The computed empty attachment of the original space. -/
def emptyCellSpace : TopCat.{1} := CellFamilyAttachment.space archSpace 1 emptyAttachingMaps

/-- Universal descent returns the empty attachment to the original space. -/
def emptyReturn : emptyCellSpace ⟶ archSpace :=
  CellFamilyAttachment.desc archSpace 1 emptyAttachingMaps (𝟙 archSpace)
    (fun i => Fin.elim0 i.down) (by intro i; exact Fin.elim0 i.down)

private theorem emptyReturn_leftInverse :
    CellFamilyAttachment.inclusion archSpace 1 emptyAttachingMaps ≫ emptyReturn =
      𝟙 archSpace := by
  exact CellFamilyAttachment.inclusion_desc archSpace 1 emptyAttachingMaps (𝟙 archSpace)
    (fun i => Fin.elim0 i.down) (by intro i; exact Fin.elim0 i.down)

/-- The actual pushout inclusion and universal descent are inverse for the empty family. -/
def emptyAttachmentIso : archSpace ≅ emptyCellSpace where
  hom := CellFamilyAttachment.inclusion archSpace 1 emptyAttachingMaps
  inv := emptyReturn
  hom_inv_id := by exact emptyReturn_leftInverse
  inv_hom_id := by
    let j : archSpace ⟶ emptyCellSpace :=
      CellFamilyAttachment.inclusion archSpace 1 emptyAttachingMaps
    have hj : j ≫ emptyReturn = 𝟙 archSpace := emptyReturn_leftInverse
    have hX : j ≫ (emptyReturn ≫ j) = j ≫ 𝟙 emptyCellSpace := by
      calc
        j ≫ (emptyReturn ≫ j) = (j ≫ emptyReturn) ≫ j :=
          (Category.assoc j emptyReturn j).symm
        _ = (𝟙 archSpace) ≫ j :=
          congrArg (fun f : archSpace ⟶ archSpace => f ≫ j) hj
        _ = j := Category.id_comp j
        _ = j ≫ 𝟙 emptyCellSpace := (Category.comp_id j).symm
    exact CellFamilyAttachment.hom_ext archSpace 1 emptyAttachingMaps
      (f := emptyReturn ≫ j) (g := 𝟙 emptyCellSpace) hX
      (by intro i; exact Fin.elim0 i.down)

/-- The empty comparison retains the literal original-space pushout leg. -/
theorem emptyIsoForwardClient :
    emptyAttachmentIso.hom =
      pushout.inr (CellFamilyAttachment.boundaryToDisks EmptyCellIndex 1)
        (CellFamilyAttachment.attachingMap archSpace 1 emptyAttachingMaps) := rfl

section Subgroup

variable (X : TopCat.{1}) (x : X) (P : Subgroup (FundamentalGroup X x))

/-- Representatives of original subgroup elements are killed by the all-element family. -/
theorem subgroupRepresentativeClient (p : P) :
    LoopCellAttachment.pi1Map X x P
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (FundamentalGroup.loopRepresentative p.val))) = 1 := by
  rw [FundamentalGroup.fromPath_loopRepresentative]
  exact LoopCellAttachment.pi1Map_kills X x P p

/-- Quotient factorization evaluates on representatives in the original vertex group. -/
theorem quotientRepresentativeClient [P.Normal] (q : FundamentalGroup X x) :
    LoopCellAttachment.quotientPi1Map X x P
        (QuotientGroup.mk' P (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (FundamentalGroup.loopRepresentative q)))) =
      LoopCellAttachment.pi1Map X x P q := by
  have h := congrArg (fun f : FundamentalGroup X x →*
      FundamentalGroup (LoopCellAttachment.space X x P) (LoopCellAttachment.inclusion X x P x) =>
        f (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (FundamentalGroup.loopRepresentative q))))
    (LoopCellAttachment.quotientPi1Map_comp_mk X x P)
  simpa only [MonoidHom.comp_apply, FundamentalGroup.fromPath_loopRepresentative] using h

end Subgroup

end AlgebraicTopology.LoopCellAttachmentTests
