/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusDeformation
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellAttachment
public import MathlibExt.AlgebraicTopology.PlusConstruction.SquarePerimeterWinding
public import Mathlib.Topology.Homotopy.Path

/-!
# Original subgroup loops in the actual annuli

The radius-five-eighths section places the same original square perimeter
in the actual annulus indexed by its original subgroup element. Its
characteristic map into the outer region retracts through the original
attaching map, so its based class retracts to that same subgroup element.
The existing outer-region deformation also supplies the actual path to
the inclusion of the original basepoint. Its constant retracted-path
calculation remains the full-collar normalization obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))

/-- The original indexed boundary placed at radius five eighths in its actual annulus. -/
def boundaryToAnnulus (p : P) :
    C(classicalCellSquareBoundary.{u}, CellCollarCover.annulus P 1) :=
  (CellAnnulusDeformation.boundarySection P 1).comp
    (TopCat.sigmaι (fun _ : P => (classicalCellDiskPair.{u} 2).snd) p).hom

theorem boundaryToAnnulus_apply (p : P) (b : classicalCellSquareBoundary.{u}) :
    boundaryToAnnulus X x P p b =
      CellAnnulusDeformation.boundarySection P 1 ⟨p, b⟩ :=
  rfl

/-- Its actual original direction is the same boundary point in the same original summand. -/
theorem direction_boundaryToAnnulus (p : P) (b : classicalCellSquareBoundary.{u}) :
    CellAnnulusDeformation.direction P 1 (boundaryToAnnulus X x P p b) = ⟨p, b⟩ :=
  CellAnnulusDeformation.direction_boundarySection 1 ⟨p, b⟩

/-- The same original bottom-left corner at the actual annular section. -/
def annulusBasepoint (p : P) : CellCollarCover.annulus P 1 :=
  boundaryToAnnulus X x P p classicalCellSquareBottomLeft.{u}

/-- The original perimeter mapped into the actual annulus, with its literal image basepoint. -/
def annulusPerimeter (p : P) :
    Path (annulusBasepoint X x P p) (annulusBasepoint X x P p) :=
  classicalCellSquarePerimeter.{u}.map (boundaryToAnnulus X x P p).continuous

/-- Its class in the original based End group of the actual family annulus. -/
def annulusPerimeterClass (p : P) :
    FundamentalGroup (CellCollarCover.annulus P 1) (annulusBasepoint X x P p) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (annulusPerimeter X x P p))

/-- The actual annular section followed by its characteristic map into the actual outer region. -/
def outerBoundaryMap (p : P) :
    C(classicalCellSquareBoundary.{u},
      CellCollarCover.U X 1 (attachingMap X x P)) :=
  (CellAnnulusDeformation.toOuter X 1 (attachingMap X x P)).comp
    (boundaryToAnnulus X x P p)

/-- Retraction of this actual characteristic map is exactly the original attaching map. -/
theorem outerBoundaryMap_retraction (p : P) :
    (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom.comp
        (outerBoundaryMap X x P p) =
      (attachingMap X x P p).hom := by
  apply ContinuousMap.ext
  intro b
  have h := CellAnnulusDeformation.retraction_toOuter X 1 (attachingMap X x P)
    (boundaryToAnnulus X x P p b)
  exact h.trans ((congrArg (CellFamilyAttachment.attachingMap X 1 (attachingMap X x P))
    (direction_boundaryToAnnulus X x P p b)).trans
      (CellFamilyAttachment.attachingMap_apply X 1 (attachingMap X x P) p b))

/-- The literal actual outer-region image of the annular basepoint. -/
def outerBasepoint (p : P) : CellCollarCover.U X 1 (attachingMap X x P) :=
  outerBoundaryMap X x P p classicalCellSquareBottomLeft.{u}

/-- The original-space retraction sends this actual annular basepoint to the original x. -/
theorem retraction_outerBasepoint (p : P) :
    CellCollarDeformation.retractionU X 1 (attachingMap X x P)
        (outerBasepoint X x P p) = x :=
  (DFunLike.congr_fun (outerBoundaryMap_retraction X x P p)
    classicalCellSquareBottomLeft.{u}).trans (attachingMap_basepoint X x P p)

/-- The same original perimeter in the actual outer region. -/
def outerPerimeter (p : P) :
    Path (outerBasepoint X x P p) (outerBasepoint X x P p) :=
  classicalCellSquarePerimeter.{u}.map (outerBoundaryMap X x P p).continuous

/-- Its class in the original outer-region based End group. -/
def outerPerimeterClass (p : P) :
    FundamentalGroup (CellCollarCover.U X 1 (attachingMap X x P))
      (outerBasepoint X x P p) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (outerPerimeter X x P p))

/-- The actual characteristic maps the same original perimeter class to this outer class. -/
theorem outerPerimeterClass_eq_map (p : P) :
    outerPerimeterClass X x P p =
      FundamentalGroup.mapOfEq (outerBoundaryMap X x P p) rfl
        classicalCellSquarePerimeterClass.{u} := by
  let U : Type u := CellCollarCover.U X 1 (attachingMap X x P)
  let f : C(classicalCellSquareBoundary.{u}, U) := outerBoundaryMap X x P p
  let b : U := outerBasepoint X x P p
  have hb : f classicalCellSquareBottomLeft.{u} = b := rfl
  have hPath : (classicalCellSquarePerimeter.{u}.map f.continuous).cast
      hb.symm hb.symm = outerPerimeter X x P p := rfl
  have hClass : (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u}) f).cast
        hb.symm hb.symm = Path.Homotopic.Quotient.mk (outerPerimeter X x P p) :=
    (congrArg
      (fun q : Path.Homotopic.Quotient
          (f classicalCellSquareBottomLeft.{u}) (f classicalCellSquareBottomLeft.{u}) =>
        q.cast hb.symm hb.symm)
      (Path.Homotopic.Quotient.mk_map classicalCellSquarePerimeter.{u} f).symm).trans
        ((Path.Homotopic.Quotient.mk_cast (classicalCellSquarePerimeter.{u}.map f.continuous)
          hb.symm hb.symm).symm.trans (congrArg Path.Homotopic.Quotient.mk hPath))
  have hMap : FundamentalGroup.mapOfEq f hb classicalCellSquarePerimeterClass.{u} =
      outerPerimeterClass X x P p :=
    (FundamentalGroup.mapOfEq_apply f hb classicalCellSquarePerimeterClass.{u}).trans
      (congrArg (fun q : Path.Homotopic.Quotient b b => FundamentalGroup.fromPath q) hClass)
  exact hMap.symm

private theorem annulus_mapOfEq_congr {A B : Type u}
    [TopologicalSpace A] [TopologicalSpace B] {a : A} {b : B} {f g : C(A, B)}
    (h : f = g) (hf : f a = b) (hg : g a = b) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  cases h
  rfl

/-- Retraction of the original annular outer class is the SAME original subgroup element. -/
theorem retraction_outerPerimeterClass (p : P) :
    FundamentalGroup.mapOfEq
        (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
        (retraction_outerBasepoint X x P p) (outerPerimeterClass X x P p) = p.val := by
  let U : Type u := CellCollarCover.U X 1 (attachingMap X x P)
  let f : C(classicalCellSquareBoundary.{u}, U) := outerBoundaryMap X x P p
  let r : C(U, X) := (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
  let b : U := outerBasepoint X x P p
  have hb : f classicalCellSquareBottomLeft.{u} = b := rfl
  have h0 : r b = x := retraction_outerBasepoint X x P p
  have hLeft : (r.comp f) classicalCellSquareBottomLeft.{u} = x :=
    (congrArg r hb).trans h0
  have hOuter : outerPerimeterClass X x P p =
      FundamentalGroup.mapOfEq f hb classicalCellSquarePerimeterClass.{u} := by
    exact outerPerimeterClass_eq_map X x P p
  have hCompose : FundamentalGroup.mapOfEq r h0
      (FundamentalGroup.mapOfEq f hb classicalCellSquarePerimeterClass.{u}) =
        FundamentalGroup.mapOfEq (r.comp f) hLeft classicalCellSquarePerimeterClass.{u} :=
    (MonoidHom.comp_apply (FundamentalGroup.mapOfEq r h0) (FundamentalGroup.mapOfEq f hb)
      classicalCellSquarePerimeterClass.{u}).symm.trans
        (congrArg (fun g : FundamentalGroup classicalCellSquareBoundary.{u}
            classicalCellSquareBottomLeft.{u} →* FundamentalGroup X x =>
          g classicalCellSquarePerimeterClass.{u})
          (FundamentalGroup.mapOfEq_comp f r hb h0 hLeft).symm)
  have hRetraction : r.comp f = (attachingMap X x P p).hom :=
    outerBoundaryMap_retraction X x P p
  have hChange := annulus_mapOfEq_congr hRetraction hLeft (attachingMap_basepoint X x P p)
  have hChanged : FundamentalGroup.mapOfEq (r.comp f) hLeft
      classicalCellSquarePerimeterClass.{u} =
        FundamentalGroup.mapOfEq (attachingMap X x P p).hom
          (attachingMap_basepoint X x P p) classicalCellSquarePerimeterClass.{u} :=
    congrArg (fun g : FundamentalGroup classicalCellSquareBoundary.{u}
        classicalCellSquareBottomLeft.{u} →* FundamentalGroup X x =>
      g classicalCellSquarePerimeterClass.{u}) hChange
  have hAttaching : FundamentalGroup.mapOfEq (attachingMap X x P p).hom
      (attachingMap_basepoint X x P p) classicalCellSquarePerimeterClass.{u} = p.val := by
    exact attachingMap_perimeter X x P p
  exact (congrArg (fun q : FundamentalGroup U b => FundamentalGroup.mapOfEq r h0 q)
    hOuter).trans (hCompose.trans (hChanged.trans hAttaching))

/-- The ACTUAL computed deformation traces a path to the inclusion of the original basepoint. -/
def outerBasepointPath (p : P) :
    Path (outerBasepoint X x P p)
      (CellCollarDeformation.inclusionU X 1 (attachingMap X x P) x) :=
  ((CellCollarDeformation.deformationU X 1 (attachingMap X x P)).toHomotopy.evalAt
    (outerBasepoint X x P p)).cast rfl
      (congrArg (CellCollarDeformation.inclusionU X 1 (attachingMap X x P))
        (retraction_outerBasepoint X x P p)).symm

/-- This path retains the actual original outer-region deformation at every time. -/
theorem outerBasepointPath_apply (p : P) (t : I) :
    outerBasepointPath X x P p t =
      CellCollarDeformation.deformationU X 1 (attachingMap X x P)
        (t, outerBasepoint X x P p) :=
  rfl

/-- The actual annular class transported in the original End convention to the included x. -/
def transportedOuterPerimeterClass (p : P) :
    FundamentalGroup (CellCollarCover.U X 1 (attachingMap X x P))
      (CellCollarDeformation.inclusionU X 1 (attachingMap X x P) x) :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath (outerBasepointPath X x P p)
    (outerPerimeterClass X x P p)

end AlgebraicTopology.LoopCellAttachment

end

end
