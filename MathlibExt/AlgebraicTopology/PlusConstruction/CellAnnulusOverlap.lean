/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusComponents
public import MathlibExt.AlgebraicTopology.PlusConstruction.AnnulusLoopClasses
public import MathlibExt.Topology.Homotopy.VanKampen
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The original annulus and the actual open overlap

The original restricted disk characteristic map gives a homeomorphism from
the literal indexed annulus to the actual intersection of the two collar
regions. Its composition with the canonical left inclusion is the existing
annular characteristic into the outer region. No comparison homeomorphism is
an input, and arbitrary indices and all `n + 1` dimensions are retained.

For the actual subgroup-indexed two-cell family, the component perimeter and
the attaching-loop annular perimeter have the same original points. Their
proved basepoint equality supplies both endpoint casts. The existing annular
characteristic then maps that same original End class to the original outer
perimeter class.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.CellAnnulusOverlap

section Overlap

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The original disk restriction gives the actual annulus-to-overlap homeomorphism. -/
def homeomorph :
    CellCollarCover.annulus ι n ≃ₜ
      ↥(CellCollarCover.U X n a ∩ CellCollarCover.V X n a) :=
  (Homeomorph.setCongr
    (CellCollarCover.diskInclusion_preimage_intersection X n a).symm).trans
      (IsHomeomorph.homeomorph
        ((CellCollarCover.U X n a ∩ CellCollarCover.V X n a).restrictPreimage
          (CellFamilyAttachment.diskInclusion X n a))
        (CellCollarCover.isHomeomorph_intersection_diskRestriction X n a))

/-- The homeomorphism retains the original characteristic value of the same disk point. -/
theorem homeomorph_val (z : CellCollarCover.annulus ι n) :
    (homeomorph X n a z).val = CellFamilyAttachment.diskInclusion X n a z.val := by
  rfl

/-- The inverse returns the original annular disk point mapping to the selected overlap point. -/
theorem diskInclusion_homeomorph_symm
    (z : ↥(CellCollarCover.U X n a ∩ CellCollarCover.V X n a)) :
    CellFamilyAttachment.diskInclusion X n a ((homeomorph X n a).symm z).val = z.val := by
  have hValue := homeomorph_val X n a ((homeomorph X n a).symm z)
  have hInverse : (homeomorph X n a ((homeomorph X n a).symm z)).val = z.val :=
    congrArg
      (fun y : ↥(CellCollarCover.U X n a ∩ CellCollarCover.V X n a) => y.val)
      ((homeomorph X n a).apply_symm_apply z)
  exact hValue.symm.trans hInverse

/-- The canonical original left inclusion followed by the homeomorphism is the existing
annular characteristic map into the actual outer region. -/
theorem inclusionLeft_comp_homeomorph :
    (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterLeft
        (CellCollarCover.U X n a) (CellCollarCover.V X n a)).comp
      (homeomorph X n a).toHomotopyEquiv.toFun =
        CellAnnulusDeformation.toOuter X n a := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact (homeomorph_val X n a z).trans
    (CellAnnulusDeformation.toOuter_val X n a z).symm

end Overlap

section OriginalPerimeter

variable (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))

/-- The independently constructed indexed boundary section is the original component section. -/
theorem boundaryToAnnulus_eq_component (p : P) :
    LoopCellAttachment.boundaryToAnnulus X x P p =
      (CellAnnulusCoordinates.componentInclusion 1 p).comp
        classicalCellSquareAnnulusSection.{u} := by
  apply ContinuousMap.ext
  intro b
  exact (LoopCellAttachment.boundaryToAnnulus_apply X x P p b).trans
    (CellAnnulusComponents.componentInclusion_section P p b)

/-- The original component basepoint equals the basepoint in the chosen-loop annular section. -/
theorem basepoint_eq_annulusBasepoint (p : P) :
    CellAnnulusComponents.basepoint P p = LoopCellAttachment.annulusBasepoint X x P p := by
  have hPoint :
      LoopCellAttachment.boundaryToAnnulus X x P p classicalCellSquareBottomLeft.{u} =
        CellAnnulusCoordinates.componentInclusion 1 p
          (classicalCellSquareAnnulusSection.{u} classicalCellSquareBottomLeft.{u}) :=
    DFunLike.congr_fun (boundaryToAnnulus_eq_component X x P p)
      classicalCellSquareBottomLeft.{u}
  exact hPoint.symm

/-- Both proved endpoint casts identify the same original component and annular perimeter paths. -/
theorem perimeter_cast (p : P) :
    (CellAnnulusComponents.perimeter P p).cast
        (basepoint_eq_annulusBasepoint X x P p).symm
        (basepoint_eq_annulusBasepoint X x P p).symm =
      LoopCellAttachment.annulusPerimeter X x P p := by
  apply Path.ext
  funext t
  have hCast :
      ((CellAnnulusComponents.perimeter P p).cast
          (basepoint_eq_annulusBasepoint X x P p).symm
          (basepoint_eq_annulusBasepoint X x P p).symm) t =
        CellAnnulusComponents.perimeter P p t :=
    congrFun (Path.cast_coe (CellAnnulusComponents.perimeter P p)
      (basepoint_eq_annulusBasepoint X x P p).symm
      (basepoint_eq_annulusBasepoint X x P p).symm) t
  have hFamily := CellAnnulusComponents.perimeter_apply P p t
  have hAnnulus := LoopCellAttachment.boundaryToAnnulus_apply X x P p
    (classicalCellSquarePerimeter.{u} t)
  exact hCast.trans (hFamily.trans hAnnulus.symm)

/-- The corresponding original homotopy classes agree after the same two endpoint casts. -/
theorem perimeterClass_cast (p : P) :
    Path.Homotopic.Quotient.cast
      ((CellAnnulusComponents.perimeterClass P p).asHom :
        Path.Homotopic.Quotient (CellAnnulusComponents.basepoint P p)
          (CellAnnulusComponents.basepoint P p))
        (basepoint_eq_annulusBasepoint X x P p).symm
        (basepoint_eq_annulusBasepoint X x P p).symm =
      ((LoopCellAttachment.annulusPerimeterClass X x P p).asHom :
        Path.Homotopic.Quotient (LoopCellAttachment.annulusBasepoint X x P p)
          (LoopCellAttachment.annulusBasepoint X x P p)) := by
  change (Path.Homotopic.Quotient.mk (CellAnnulusComponents.perimeter P p)).cast
      (basepoint_eq_annulusBasepoint X x P p).symm
      (basepoint_eq_annulusBasepoint X x P p).symm =
    Path.Homotopic.Quotient.mk (LoopCellAttachment.annulusPerimeter X x P p)
  exact (Path.Homotopic.Quotient.mk_cast (CellAnnulusComponents.perimeter P p)
    (basepoint_eq_annulusBasepoint X x P p).symm
    (basepoint_eq_annulusBasepoint X x P p).symm).symm.trans
      (congrArg Path.Homotopic.Quotient.mk (perimeter_cast X x P p))

/-- The existing annular characteristic maps the original component basepoint to the outer one. -/
theorem toOuter_basepoint (p : P) :
    CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)
        (CellAnnulusComponents.basepoint P p) =
      LoopCellAttachment.outerBasepoint X x P p := by
  let s := CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)
  have hPoint : s (CellAnnulusComponents.basepoint P p) =
      s (LoopCellAttachment.annulusBasepoint X x P p) :=
    congrArg s (basepoint_eq_annulusBasepoint X x P p)
  exact hPoint

/-- The actual mapped component perimeter is the original outer path, with both original casts. -/
theorem toOuter_perimeter (p : P) :
    ((CellAnnulusComponents.perimeter P p).map
        (CellAnnulusDeformation.toOuter X 1
          (LoopCellAttachment.attachingMap X x P)).continuous).cast
        (toOuter_basepoint X x P p).symm (toOuter_basepoint X x P p).symm =
      LoopCellAttachment.outerPerimeter X x P p := by
  let s := CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)
  apply Path.ext
  funext t
  have hCast :
      (((CellAnnulusComponents.perimeter P p).map s.continuous).cast
          (toOuter_basepoint X x P p).symm (toOuter_basepoint X x P p).symm) t =
        s (CellAnnulusComponents.perimeter P p t) :=
    congrFun (Path.cast_coe ((CellAnnulusComponents.perimeter P p).map s.continuous)
      (toOuter_basepoint X x P p).symm (toOuter_basepoint X x P p).symm) t
  have hFamily := CellAnnulusComponents.perimeter_apply P p t
  have hAnnulus := LoopCellAttachment.boundaryToAnnulus_apply X x P p
    (classicalCellSquarePerimeter.{u} t)
  exact hCast.trans (congrArg s (hFamily.trans hAnnulus.symm))

/-- The original equality-pointed map sends the same component End class to the outer class. -/
theorem toOuter_perimeterClass (p : P) :
    FundamentalGroup.mapOfEq
        (CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P))
        (toOuter_basepoint X x P p) (CellAnnulusComponents.perimeterClass P p) =
      LoopCellAttachment.outerPerimeterClass X x P p := by
  let A : Type u := CellCollarCover.annulus P 1
  let U : Type u := CellCollarCover.U X 1 (LoopCellAttachment.attachingMap X x P)
  let s : C(A, U) :=
    CellAnnulusDeformation.toOuter X 1 (LoopCellAttachment.attachingMap X x P)
  let bA : A := CellAnnulusComponents.basepoint P p
  let bU : U := LoopCellAttachment.outerBasepoint X x P p
  have hBasepoint : s bA = bU := toOuter_basepoint X x P p
  have hClass :
      ((Path.Homotopic.Quotient.mk (CellAnnulusComponents.perimeter P p)).map s).cast
          hBasepoint.symm hBasepoint.symm =
        Path.Homotopic.Quotient.mk (LoopCellAttachment.outerPerimeter X x P p) :=
    (congrArg
      (fun q : Path.Homotopic.Quotient (s bA) (s bA) =>
        q.cast hBasepoint.symm hBasepoint.symm)
      (Path.Homotopic.Quotient.mk_map (CellAnnulusComponents.perimeter P p) s).symm).trans
        ((Path.Homotopic.Quotient.mk_cast
          ((CellAnnulusComponents.perimeter P p).map s.continuous)
          hBasepoint.symm hBasepoint.symm).symm.trans
            (congrArg Path.Homotopic.Quotient.mk (toOuter_perimeter X x P p)))
  exact (FundamentalGroup.mapOfEq_apply s hBasepoint
    (CellAnnulusComponents.perimeterClass P p)).trans
      (congrArg (fun q : Path.Homotopic.Quotient bU bU => FundamentalGroup.fromPath q) hClass)

end OriginalPerimeter

end AlgebraicTopology.CellAnnulusOverlap

end
