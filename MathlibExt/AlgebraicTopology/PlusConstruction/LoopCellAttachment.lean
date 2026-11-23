/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyAttachment
public import MathlibExt.AlgebraicTopology.PlusConstruction.SquareBoundaryPerimeter
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.LoopRepresentatives
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Actual two-cells for the loops in a subgroup

Choose an original based loop for every element of the subgroup. Its actual
square-boundary map determines a family of two-cells and a canonical
inclusion of the original space. The actual characteristic disks show that
this inclusion kills every chosen element. For a normal subgroup, the
original based fundamental-group map therefore descends to the quotient.

Surjectivity, the reverse kernel inclusion, a compatible CW structure and
the homology-correcting three-cells remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))

/-- The actual attaching map represents the selected original subgroup element. -/
def attachingMap (p : P) : (classicalCellDiskPair.{u} 2).snd ⟶ X :=
  TopCat.ofHom (classicalCellSquareLoopMap (FundamentalGroup.loopRepresentative p.val))

/-- Its actual selected square corner is sent to the original basepoint. -/
@[simp]
theorem attachingMap_basepoint (p : P) :
    attachingMap X x P p classicalCellSquareBottomLeft.{u} = x :=
  classicalCellSquareLoopMap_bottomLeft (FundamentalGroup.loopRepresentative p.val)

/-- The original perimeter class maps to the selected original group element. -/
theorem attachingMap_perimeter (p : P) :
    FundamentalGroup.mapOfEq (attachingMap X x P p).hom
        (attachingMap_basepoint X x P p)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u})) = p.val := by
  change FundamentalGroup.mapOfEq
      (classicalCellSquareLoopMap (FundamentalGroup.loopRepresentative p.val))
      (attachingMap_basepoint X x P p)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u})) = p.val
  rw [classicalCellSquareLoopMap_perimeter,
    FundamentalGroup.fromPath_loopRepresentative]

/-- The actual two-cell attachment is indexed by every element of the original subgroup. -/
def space : TopCat.{u} :=
  CellFamilyAttachment.space X 1 (attachingMap X x P)

/-- The canonical inclusion of the whole original space into the computed two-cell space. -/
def inclusion : X ⟶ space X x P :=
  CellFamilyAttachment.inclusion X 1 (attachingMap X x P)

/-- The actual characteristic disk for the selected original subgroup element. -/
def cell (p : P) : (classicalCellDiskPair.{u} 2).fst ⟶ space X x P :=
  CellFamilyAttachment.cell X 1 (attachingMap X x P) p

/-- The actual chosen boundary map agrees with the corresponding characteristic disk. -/
@[reassoc]
theorem boundary_gluing (p : P) :
    attachingMap X x P p ≫ inclusion X x P =
      (classicalCellDiskPair.{u} 2).map ≫ cell X x P p :=
  CellFamilyAttachment.boundary_gluing X 1 (attachingMap X x P) p

/-- The selected point of the actual disk maps to the inclusion of the original basepoint. -/
theorem cell_basepoint (p : P) :
    cell X x P p ((classicalCellDiskPair.{u} 2).map classicalCellSquareBottomLeft.{u}) =
      inclusion X x P x := by
  have h := ConcreteCategory.congr_hom (boundary_gluing X x P p)
    classicalCellSquareBottomLeft.{u}
  simpa only [ConcreteCategory.comp_apply, attachingMap_basepoint] using h.symm

/-- The original source remains a closed subspace of the actual two-cell attachment. -/
theorem inclusion_isClosedEmbedding : IsClosedEmbedding (inclusion X x P) :=
  CellFamilyAttachment.inclusion_isClosedEmbedding X 1 (attachingMap X x P)

/-- The actual two-cell space is connected when the original source is connected. -/
theorem connectedSpace [ConnectedSpace X] : ConnectedSpace (space X x P) :=
  CellFamilyAttachment.connectedSpace X 1 (attachingMap X x P)

/-- The original based fundamental-group map, with the literal image basepoint. -/
def pi1Map : FundamentalGroup X x →* FundamentalGroup (space X x P) (inclusion X x P x) :=
  FundamentalGroup.mapOfEq (inclusion X x P).hom rfl

private theorem mapOfEq_eq_of_eq {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)} (h : f = g) (hf : f a = b) (hg : g a = b) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  cases h
  rfl

/-- Every original subgroup element is killed by its actual attached characteristic disk. -/
theorem pi1Map_kills (p : P) : pi1Map X x P p.val = 1 := by
  let a := attachingMap X x P p
  let j := inclusion X x P
  let d := (classicalCellDiskPair.{u} 2).map
  let c := cell X x P p
  let β := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u})
  have ha : a classicalCellSquareBottomLeft.{u} = x := attachingMap_basepoint X x P p
  have hc : c (d classicalCellSquareBottomLeft.{u}) = j x := cell_basepoint X x P p
  have hLeft : (j.hom.comp a.hom) classicalCellSquareBottomLeft.{u} = j x :=
    congrArg j ha
  have hRight : (c.hom.comp d.hom) classicalCellSquareBottomLeft.{u} = j x := hc
  have hMaps : j.hom.comp a.hom = c.hom.comp d.hom := by
    change (a ≫ j).hom = (d ≫ c).hom
    exact congrArg (fun f : (classicalCellDiskPair.{u} 2).snd ⟶ space X x P => f.hom)
      (boundary_gluing X x P p)
  have hClass : FundamentalGroup.mapOfEq a.hom ha β = p.val := attachingMap_perimeter X x P p
  have hDisk : FundamentalGroup.mapOfEq d.hom rfl β = 1 := Subsingleton.elim _ _
  have h := congrArg (fun f => f β) (mapOfEq_eq_of_eq hMaps hLeft hRight)
  rw [FundamentalGroup.mapOfEq_comp a.hom j.hom ha rfl hLeft,
    FundamentalGroup.mapOfEq_comp d.hom c.hom rfl hc hRight,
    MonoidHom.comp_apply, MonoidHom.comp_apply, hClass, hDisk, map_one] at h
  exact h

/-- The actual original subgroup is contained in the kernel of the canonical based map. -/
theorem subgroup_le_ker : P ≤ (pi1Map X x P).ker := by
  intro p hp
  exact pi1Map_kills X x P ⟨p, hp⟩

section Normal

variable [P.Normal]

/-- The actual based map descends to the original quotient group
after the proved kernel inclusion. -/
def quotientPi1Map : FundamentalGroup X x ⧸ P →*
    FundamentalGroup (space X x P) (inclusion X x P x) :=
  QuotientGroup.lift P (pi1Map X x P) (subgroup_le_ker X x P)

/-- The quotient homomorphism factors the same original based fundamental-group map. -/
theorem quotientPi1Map_comp_mk :
    (quotientPi1Map X x P).comp (QuotientGroup.mk' P) = pi1Map X x P :=
  QuotientGroup.lift_comp_mk' P (pi1Map X x P) (subgroup_le_ker X x P)

/-- Evaluation of the quotient homomorphism retains the original inclusion-induced map. -/
@[simp↓]
theorem quotientPi1Map_mk (p : FundamentalGroup X x) :
    quotientPi1Map X x P (QuotientGroup.mk' P p) = pi1Map X x P p :=
  rfl

end Normal

end AlgebraicTopology.LoopCellAttachment
