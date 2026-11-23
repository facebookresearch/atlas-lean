/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.AnnulusLoopTransport
public import MathlibExt.AlgebraicTopology.PlusConstruction.SquareAnnulusWinding

import Mathlib.Tactic.NormNum

/-!
# Ordinary clients for original annular loop transport

The original square boundary supplies a nontrivial perimeter in the top
subgroup. Its actual transported outer-region class retracts to that same
generator in universes zero and one. A nonconstant original component
connector tests path-transport naturality from a raw universe-one annulus
to the raw universe-zero square boundary.

The full collar includes radius one and a five-eighths trajectory whose
half-time radius is thirteen-sixteenths. The empty family in cell parameter
zero still has actual original-space points in U. The zero-dimensional
normed space also gives a concrete disk point, with no Nontrivial premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.AnnulusLoopTransportTests

/-- The original lifted square boundary, viewed as the actual input space. -/
def originalSquare : TopCat.{u} := TopCat.of classicalCellSquareBoundary.{u}

/-- Its original chosen bottom-left point. -/
def originalBasepoint : originalSquare.{u} := classicalCellSquareBottomLeft.{u}

/-- Every original square-boundary loop is in this actual top subgroup. -/
def allOriginalLoops : Subgroup (FundamentalGroup originalSquare.{u} originalBasepoint.{u}) :=
  ⊤

/-- The selected subgroup element is the same original four-edge perimeter class. -/
def perimeterMember : allOriginalLoops.{u} :=
  ⟨classicalCellSquarePerimeterClass.{u}, by
    change classicalCellSquarePerimeterClass.{u} ∈
      (⊤ : Subgroup (FundamentalGroup originalSquare.{u} originalBasepoint.{u}))
    exact Subgroup.mem_top _⟩

/-- The actual open outer region of the corresponding original all-loop cell attachment. -/
def originalU : TopCat.{u} :=
  TopCat.of (CellCollarCover.U originalSquare.{u} 1
    (LoopCellAttachment.attachingMap originalSquare.{u} originalBasepoint.{u} allOriginalLoops.{u}))

/-- The actual original-space inclusion into that outer region. -/
def originalInclusionU : originalSquare.{u} ⟶ originalU.{u} :=
  CellCollarDeformation.inclusionU originalSquare.{u} 1
    (LoopCellAttachment.attachingMap originalSquare.{u} originalBasepoint.{u} allOriginalLoops.{u})

/-- The constructed original-space retraction of that same outer region. -/
def originalRetraction : originalU.{u} ⟶ originalSquare.{u} :=
  CellCollarDeformation.retractionU originalSquare.{u} 1
    (LoopCellAttachment.attachingMap originalSquare.{u} originalBasepoint.{u} allOriginalLoops.{u})

private theorem originalRetraction_basepoint :
    originalRetraction.{u} (originalInclusionU.{u} originalBasepoint.{u}) =
      originalBasepoint.{u} :=
  LoopCellAttachment.retraction_includedBasepoint
    originalSquare.{u} originalBasepoint.{u} allOriginalLoops.{u}

/-- The actual original End class transported along its constructed outer-region basepoint path. -/
def transportedPerimeter :
    FundamentalGroup originalU.{u} (originalInclusionU.{u} originalBasepoint.{u}) :=
  LoopCellAttachment.transportedOuterPerimeterClass
    originalSquare.{u} originalBasepoint.{u} allOriginalLoops.{u} perimeterMember.{u}

/-- Retraction uses the original map and its proved original image basepoint. -/
def retractedPerimeter : FundamentalGroup originalSquare.{u} originalBasepoint.{u} :=
  FundamentalGroup.mapOfEq originalRetraction.{u}.hom
    (by exact originalRetraction_basepoint.{u}) transportedPerimeter.{u}

private theorem retractedPerimeter_eq : retractedPerimeter.{u} = perimeterMember.{u}.val :=
  LoopCellAttachment.retraction_transportedOuterPerimeterClass
    originalSquare.{u} originalBasepoint.{u} allOriginalLoops.{u} perimeterMember.{u}

private theorem retractedPerimeter_winding :
    classicalCellSquareWindingIso.{u} retractedPerimeter.{u} =
      Multiplicative.ofAdd (1 : ℤ) := by
  exact (congrArg classicalCellSquareWindingIso.{u} retractedPerimeter_eq.{u}).trans
    classicalCellSquareWindingIso_perimeter.{u}

/-- The actual selected original class is not the unit, in every carrier lift. -/
theorem originalGeneratorNontrivialClient : perimeterMember.{u}.val ≠ 1 := by
  change classicalCellSquarePerimeterClass.{u} ≠ 1
  intro h
  have hw := congrArg classicalCellSquareWindingIso.{u} h
  rw [classicalCellSquareWindingIso_perimeter] at hw
  have hUnit : classicalCellSquareWindingIso.{u} 1 = (1 : Multiplicative ℤ) :=
    classicalCellSquareWindingIso.{u}.map_one
  have hi := congrArg (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ) (hw.trans hUnit)
  norm_num at hi

/-- The actual transported universe-one class remains nontrivial in the original outer region. -/
theorem transportedGeneratorNontrivialClient : transportedPerimeter.{1} ≠ 1 := by
  intro h
  let f := FundamentalGroup.mapOfEq originalRetraction.{1}.hom
    (by exact originalRetraction_basepoint.{1})
  have hr : retractedPerimeter.{1} = 1 :=
    (congrArg f h).trans (map_one f)
  exact originalGeneratorNontrivialClient.{1} (retractedPerimeter_eq.{1}.symm.trans hr)

/-- Original universe-zero transport returns the same generator and its positive winding. -/
theorem universeZeroTransportClient :
    retractedPerimeter.{0} = perimeterMember.{0}.val ∧
      classicalCellSquareWindingIso.{0} retractedPerimeter.{0} = Multiplicative.ofAdd (1 : ℤ) ∧
      classicalCellSquareAnnulusWindingIso.{0} classicalCellSquareAnnulusPerimeterClass.{0} =
        Multiplicative.ofAdd (1 : ℤ) := by
  exact ⟨retractedPerimeter_eq.{0}, retractedPerimeter_winding.{0},
    classicalCellSquareAnnulusWindingIso_perimeter.{0}⟩

/-- The same actual cell and component constructions retain carrier universe one. -/
theorem universeOneTransportClient :
    retractedPerimeter.{1} = perimeterMember.{1}.val ∧
      classicalCellSquareWindingIso.{1} retractedPerimeter.{1} = Multiplicative.ofAdd (1 : ℤ) ∧
      classicalCellSquareAnnulusWindingIso.{1} classicalCellSquareAnnulusPerimeterClass.{1} =
        Multiplicative.ofAdd (1 : ℤ) := by
  exact ⟨retractedPerimeter_eq.{1}, retractedPerimeter_winding.{1},
    classicalCellSquareAnnulusWindingIso_perimeter.{1}⟩

/-- Both actual annular summands retain their original selected element and boundary point. -/
theorem indexedAnnulusUniversesClient :
    CellAnnulusDeformation.direction allOriginalLoops.{0} 1
        (LoopCellAttachment.annulusBasepoint
          originalSquare.{0} originalBasepoint.{0} allOriginalLoops.{0} perimeterMember.{0}) =
      (⟨perimeterMember.{0}, classicalCellSquareBottomLeft.{0}⟩ :
        CellFamilyAttachment.boundaries allOriginalLoops.{0} 1) ∧
      CellAnnulusDeformation.direction allOriginalLoops.{1} 1
        (LoopCellAttachment.annulusBasepoint
          originalSquare.{1} originalBasepoint.{1} allOriginalLoops.{1} perimeterMember.{1}) =
        (⟨perimeterMember.{1}, classicalCellSquareBottomLeft.{1}⟩ :
          CellFamilyAttachment.boundaries allOriginalLoops.{1} 1) := by
  exact ⟨LoopCellAttachment.direction_boundaryToAnnulus
      originalSquare.{0} originalBasepoint.{0} allOriginalLoops.{0} perimeterMember.{0}
      classicalCellSquareBottomLeft.{0},
    LoopCellAttachment.direction_boundaryToAnnulus
      originalSquare.{1} originalBasepoint.{1} allOriginalLoops.{1} perimeterMember.{1}
      classicalCellSquareBottomLeft.{1}⟩

/-- The actual characteristic disks glue the original chosen corner in both carrier universes. -/
theorem cellGluingUniversesClient :
    LoopCellAttachment.cell
        originalSquare.{0} originalBasepoint.{0} allOriginalLoops.{0} perimeterMember.{0}
        ((classicalCellDiskPair.{0} 2).map classicalCellSquareBottomLeft.{0}) =
      LoopCellAttachment.inclusion
        originalSquare.{0} originalBasepoint.{0} allOriginalLoops.{0} originalBasepoint.{0} ∧
      LoopCellAttachment.cell
          originalSquare.{1} originalBasepoint.{1} allOriginalLoops.{1} perimeterMember.{1}
          ((classicalCellDiskPair.{1} 2).map classicalCellSquareBottomLeft.{1}) =
        LoopCellAttachment.inclusion
          originalSquare.{1} originalBasepoint.{1} allOriginalLoops.{1} originalBasepoint.{1} := by
  exact ⟨LoopCellAttachment.cell_basepoint
      originalSquare.{0} originalBasepoint.{0} allOriginalLoops.{0} perimeterMember.{0},
    LoopCellAttachment.cell_basepoint
      originalSquare.{1} originalBasepoint.{1} allOriginalLoops.{1} perimeterMember.{1}⟩

/-- The raw map lowers only the lift, retaining the same original sphere vector and topology. -/
def lowerSquare : C(classicalCellSquareBoundary.{1}, classicalCellSquareBoundary.{0}) where
  toFun z := ULift.up z.down
  continuous_toFun := by exact continuous_uliftUp.comp continuous_uliftDown

/-- A raw universe-one annulus maps by its original direction to the universe-zero boundary. -/
def lowerAnnulusDirection : C(classicalCellSquareAnnulus.{1}, classicalCellSquareBoundary.{0}) :=
  lowerSquare.comp classicalCellSquareAnnulusDirection.{1}

/-- The component connector has a different actual endpoint from its original bottom-left base. -/
def selectedComponentPoint : classicalCellSquareAnnulus.{1} :=
  classicalCellSquareAnnulusSection.{1} classicalCellSquareTopRight.{1}

/-- Naturality uses an actual nonconstant connector and original End class across raw universes. -/
theorem mixedUniverseNaturalityClient :
    FundamentalGroup.map lowerAnnulusDirection selectedComponentPoint
        (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (classicalCellSquareAnnulusConnector selectedComponentPoint)
          classicalCellSquareAnnulusPerimeterClass.{1}) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((classicalCellSquareAnnulusConnector selectedComponentPoint).map
          lowerAnnulusDirection.continuous)
        (FundamentalGroup.map lowerAnnulusDirection classicalCellSquareAnnulusBasepoint.{1}
          classicalCellSquareAnnulusPerimeterClass.{1}) ∧
      selectedComponentPoint ≠ classicalCellSquareAnnulusBasepoint.{1} := by
  refine ⟨FundamentalGroup.map_fundamentalGroupMulEquivOfPath lowerAnnulusDirection
    (classicalCellSquareAnnulusConnector selectedComponentPoint)
    classicalCellSquareAnnulusPerimeterClass.{1}, ?_⟩
  intro h
  have hd := congrArg classicalCellSquareAnnulusDirection.{1} h
  have hTop : classicalCellSquareAnnulusDirection.{1} selectedComponentPoint =
      classicalCellSquareTopRight.{1} :=
    classicalCellSquareAnnulusDirection_section classicalCellSquareTopRight.{1}
  rw [hTop, classicalCellSquareAnnulusDirection_basepoint] at hd
  have hx := congrArg (classicalCellSquareCoord 0) hd
  norm_num [classicalCellSquareCoord, classicalCellSquareTopRight,
    classicalCellSquareBottomLeft, classicalCellSquareVertex] at hx

/-- The concrete observation time in the original unit interval. -/
def halfTime : I := ⟨(1 : ℝ) / 2, by norm_num⟩

/-- The inner starting radius lies in the actual full collar. -/
def startingRadius : TopPair.cellCollarRadii := ⟨(5 : ℝ) / 8, by constructor <;> norm_num⟩

/-- The original top-right sphere point scaled inside its actual controlled disk collar. -/
def controlledPoint (r : TopPair.cellCollarRadii) :
    (TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).neighborhood :=
  TopPair.closedUnitBallControlledScaledBoundary.{1} (Fin 2 → ℝ)
    (classicalCellSquareTopRight.{1}, r)

private theorem controlledPoint_norm (r : TopPair.cellCollarRadii) :
    ‖(controlledPoint r).1.down.val‖ = (r : ℝ) := by
  exact (congrArg (fun z : (classicalCellDiskPair.{1} 2).fst => ‖z.down.val‖)
    (TopPair.closedUnitBallControlledScaledBoundary_val (Fin 2 → ℝ)
      classicalCellSquareTopRight.{1} r)).trans
    (TopPair.closedUnitBallScaledBoundary_norm (Fin 2 → ℝ) classicalCellSquareTopRight.{1} r)

/-- Radius one is the actual original boundary, fixed by the original controlled deformation. -/
theorem fullBoundaryRadiusClient (t : I) :
    (controlledPoint TopPair.cellCollarRadiusOne).1 =
        (classicalCellDiskPair.{1} 2).map classicalCellSquareTopRight.{1} ∧
      (TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).neighborhoodDeformation
          (t, controlledPoint TopPair.cellCollarRadiusOne) =
        controlledPoint TopPair.cellCollarRadiusOne ∧
      (TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).retraction
          (controlledPoint TopPair.cellCollarRadiusOne) = classicalCellSquareTopRight.{1} := by
  refine ⟨(TopPair.closedUnitBallControlledScaledBoundary_val (Fin 2 → ℝ)
    classicalCellSquareTopRight.{1} TopPair.cellCollarRadiusOne).trans
      (TopPair.closedUnitBallScaledBoundary_radiusOne (Fin 2 → ℝ)
        classicalCellSquareTopRight.{1}), ?_,
    TopPair.closedUnitBallRetraction_controlledScaledBoundary (Fin 2 → ℝ)
      classicalCellSquareTopRight.{1} TopPair.cellCollarRadiusOne⟩
  have h := TopPair.closedUnitBallNeighborhoodDeformation_scaledBoundary (Fin 2 → ℝ)
    t classicalCellSquareTopRight.{1} TopPair.cellCollarRadiusOne
  exact h.trans (congrArg (fun r => controlledPoint r)
    (TopPair.cellCollarRadiusLine_radiusOne t))

/-- The original radial trajectory leaves the annulus while retaining the full-collar retraction. -/
theorem fullCollarExcursionClient :
    ‖((TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).neighborhoodDeformation
        (halfTime, controlledPoint startingRadius)).1.down.val‖ = (13 : ℝ) / 16 ∧
      (TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).retraction
          ((TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).neighborhoodDeformation
            (halfTime, controlledPoint startingRadius)) = classicalCellSquareTopRight.{1} ∧
      ((TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).neighborhoodDeformation
          (halfTime, controlledPoint startingRadius)).1 ∉
        TopPair.closedUnitBallAnnulus.{1} (Fin 2 → ℝ) := by
  have hn :
      ‖((TopPair.closedUnitBallNDRData.{1} (Fin 2 → ℝ)).neighborhoodDeformation
        (halfTime, controlledPoint startingRadius)).1.down.val‖ = (13 : ℝ) / 16 := by
    calc
      _ = (1 - (halfTime : ℝ)) * ‖(controlledPoint startingRadius).1.down.val‖ +
          (halfTime : ℝ) :=
        TopPair.closedUnitBallNeighborhoodDeformation_norm (Fin 2 → ℝ)
          halfTime (controlledPoint startingRadius)
      _ = (13 : ℝ) / 16 := by
        rw [controlledPoint_norm]
        norm_num [halfTime, startingRadius]
  refine ⟨hn, (TopPair.closedUnitBallNeighborhoodDeformation_retraction (Fin 2 → ℝ)
    halfTime (controlledPoint startingRadius)).trans
      (TopPair.closedUnitBallRetraction_controlledScaledBoundary (Fin 2 → ℝ)
        classicalCellSquareTopRight.{1} startingRadius), ?_⟩
  intro hAnnulus
  have hlt := hAnnulus.2
  rw [hn] at hlt
  norm_num at hlt

/-- The actual empty degree-zero family has the concrete Fin 0 index. -/
def emptyMaps (i : Fin 0) : (classicalCellDiskPair.{0} 1).snd ⟶ originalSquare.{0} :=
  Fin.elim0 i

/-- Its actual outer region still contains the original square-boundary points. -/
def emptyU : TopCat.{0} := TopCat.of (CellCollarCover.U originalSquare.{0} 0 emptyMaps)

/-- A constructed original-space point of that actual empty-family outer region. -/
def emptyUPoint : emptyU :=
  CellCollarDeformation.inclusionU originalSquare.{0} 0 emptyMaps originalBasepoint.{0}

/-- The all-U theorem applies in n=0 to the empty family, with an actual inhabited point fixture. -/
theorem emptyFamilyDegreeZeroClient (t : I) :
    CellCollarDeformation.retractionU originalSquare.{0} 0 emptyMaps
        (CellCollarDeformation.deformationU originalSquare.{0} 0 emptyMaps (t, emptyUPoint)) =
      originalBasepoint.{0} ∧
      CellCollarDeformation.deformationU originalSquare.{0} 0 emptyMaps (t, emptyUPoint) =
        emptyUPoint ∧
      ∀ z : emptyU, CellCollarDeformation.retractionU originalSquare.{0} 0 emptyMaps
          (CellCollarDeformation.deformationU originalSquare.{0} 0 emptyMaps (t, z)) =
        CellCollarDeformation.retractionU originalSquare.{0} 0 emptyMaps z := by
  let i := CellCollarDeformation.inclusionU originalSquare.{0} 0 emptyMaps
  let r := CellCollarDeformation.retractionU originalSquare.{0} 0 emptyMaps
  have hr : r emptyUPoint = originalBasepoint.{0} :=
    (TopCat.comp_app i r originalBasepoint.{0}).symm.trans
      (ConcreteCategory.congr_hom
        (CellCollarDeformation.inclusionU_retractionU originalSquare.{0} 0 emptyMaps)
        originalBasepoint.{0})
  exact ⟨(CellCollarDeformation.retractionU_deformationU
      originalSquare.{0} 0 emptyMaps t emptyUPoint).trans hr,
    CellCollarDeformation.deformationU_inclusion
      originalSquare.{0} 0 emptyMaps t originalBasepoint.{0},
    fun z => CellCollarDeformation.retractionU_deformationU originalSquare.{0} 0 emptyMaps t z⟩

/-- The original zero vector in the actual closed ball of the empty-coordinate normed space. -/
def zeroNormDisk : (TopPair.closedBallPair.{1} (0 : Fin 0 → ℝ) 1).fst :=
  ULift.up ⟨0, by simp⟩

/-- Generic norm helpers admit Fin 0 → ℝ: its real zero disk has control one and no collar point. -/
theorem emptyNormSpaceClient :
    (TopPair.closedUnitBallControl (Fin 0 → ℝ) zeroNormDisk : ℝ) = 1 ∧
      TopPair.closedUnitBallRadialScale (0 : Fin 0 → ℝ) = 2 ∧
      zeroNormDisk ∉ (TopPair.closedUnitBallNDRData.{1} (Fin 0 → ℝ)).neighborhood := by
  refine ⟨?_, ?_, ?_⟩
  · change (Set.projIcc 0 1 zero_le_one
      (2 * (1 - ‖(0 : Fin 0 → ℝ)‖)) : ℝ) = 1
    norm_num [Set.coe_projIcc]
  · norm_num [TopPair.closedUnitBallRadialScale]
  · intro hz
    have hc : TopPair.closedUnitBallControl (Fin 0 → ℝ) zeroNormDisk < 1 :=
      ((TopPair.closedUnitBallNDRData.{1} (Fin 0 → ℝ)).mem_neighborhood zeroNormDisk).mp hz
    have hn := (TopPair.closedUnitBallControl_lt_one_iff zeroNormDisk).mp hc
    change (1 : ℝ) / 2 < ‖(0 : Fin 0 → ℝ)‖ at hn
    norm_num at hn

end AlgebraicTopology.AnnulusLoopTransportTests
