/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellAttachment
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CellFamilyModel

/-!
# The original loop-cell specialization of the common cell-family model

The same matched boundary and disk adjoints, literal simplicial pushout,
original characteristic disks and counit maps specialize the generic
classical cell-family construction at n=1. Its shared cofibrant pushout
comparison supplies the original weak-equivalence statements.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open AlgebraicTopology Topology Topology.CWComplex
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

universe u

public section

namespace AlgebraicTopology.LoopCellSimplicialModel

/-- One entire simplicial boundary for each member of the original subgroup. -/
abbrev boundaries (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  ∐ fun _ : P => (SSet.boundary.{u} 2).toSSet

/-- One entire standard two-simplex for each member of the original subgroup. -/
abbrev disks (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  ∐ fun _ : P => (Δ[2] : SSet.{u})

/-- The literal coproduct of the standard boundary inclusions. -/
def boundarySum (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    boundaries X x P ⟶ disks X x P :=
  CategoryTheory.Limits.Sigma.map (fun _ : P => (SSet.boundary.{u} 2).ι)

/-- The adjoints of the original attaching maps through the same matched boundary map. -/
def attaching (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    boundaries X x P ⟶ TopCat.toSSet.obj X := by
  exact CellFamilySimplicialModel.attaching X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The adjoints of all original whole characteristic disks through the same matched disk map. -/
def diskMates (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    disks X x P ⟶ TopCat.toSSet.obj (LoopCellAttachment.space X x P) := by
  exact CellFamilySimplicialModel.diskMates X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The literal simplicial pushout of the original attaching-map adjoints. -/
abbrev model (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  CellFamilySimplicialModel.model X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The actual old singular-space inclusion into that pushout. -/
def oldInclusion (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    TopCat.toSSet.obj X ⟶ model X x P := by
  exact CellFamilySimplicialModel.oldInclusion X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The actual whole family of new two-disks in that pushout. -/
def newDisks (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    disks X x P ⟶ model X x P := by
  exact CellFamilySimplicialModel.newDisks X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The adjoints retain the entire original boundary-gluing square. -/
theorem adjunctSquare (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    boundarySum X x P ≫ diskMates X x P =
      attaching X x P ≫ TopCat.toSSet.map (LoopCellAttachment.inclusion X x P) := by
  have h := CellFamilySimplicialModel.adjunctSquare X 1 P (LoopCellAttachment.attachingMap X x P)
  rw [CellFamilySimplicialModel.boundarySum_eq] at h
  exact h

/-- The map to the singular set of the same original two-cell attachment. -/
def toSingular (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    model X x P ⟶ TopCat.toSSet.obj (LoopCellAttachment.space X x P) := by
  exact CellFamilySimplicialModel.toSingular X 1 P (LoopCellAttachment.attachingMap X x P)

/-- Its realization followed by the actual original singular counit. -/
def realizationMap (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    SSet.toTop.obj (model X x P) ⟶ LoopCellAttachment.space X x P := by
  exact CellFamilySimplicialModel.realizationMap X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The returned model has the actual ordinary simplicial pushout square. -/
theorem isPushout (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    IsPushout (boundarySum X x P) (attaching X x P) (newDisks X x P) (oldInclusion X x P) := by
  have h := CellFamilySimplicialModel.isPushout X 1 P (LoopCellAttachment.attachingMap X x P)
  rw [CellFamilySimplicialModel.boundarySum_eq] at h
  exact h

/-- The old space retains the actual singular map of the original inclusion. -/
theorem toSingular_old (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    oldInclusion X x P ≫ toSingular X x P =
      TopCat.toSSet.map (LoopCellAttachment.inclusion X x P) := by
  exact CellFamilySimplicialModel.toSingular_old X 1 P (LoopCellAttachment.attachingMap X x P)

/-- Every whole new disk retains its original characteristic-map adjoint. -/
theorem toSingular_disks (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    newDisks X x P ≫ toSingular X x P = diskMates X x P := by
  exact CellFamilySimplicialModel.toSingular_disks X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The old realization leg is the original counit followed by the original inclusion. -/
theorem realizationMap_old (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    SSet.toTop.map (oldInclusion X x P) ≫ realizationMap X x P =
      sSetTopAdj.counit.app X ≫ LoopCellAttachment.inclusion X x P := by
  exact CellFamilySimplicialModel.realizationMap_old X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The whole original closed disk is retained through the same matched parameterization. -/
theorem realizationMap_disk (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    SSet.toTop.map (CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
        newDisks X x P) ≫ realizationMap X x P =
      (SSet.boundary.toClassicalCellDiskArrowIso 2).hom.right ≫
        LoopCellAttachment.cell X x P p := by
  exact CellFamilySimplicialModel.realizationMap_disk X 1 P (LoopCellAttachment.attachingMap X x P)
    p

/-- The actual old-space inclusion is monic in the simplicial model. -/
theorem oldInclusion_mono (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : Mono (oldInclusion X x P) := by
  exact CellFamilySimplicialModel.oldInclusion_mono X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The actual realization comparison is weak for every Hausdorff classical CW source. -/
theorem realizationMap_weak (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopCat.weakHomotopyEquivalences (realizationMap X x P) := by
  let : IsCofibrant X := CellFamilySimplicialModel.isCofibrant_of_classicalCW X
  exact CellFamilySimplicialModel.realizationMap_weak X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The actual simplicial comparison is weak on all components of the original attachment. -/
theorem toSingular_weak (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    SSet.realizationWeakEquivalences (toSingular X x P) := by
  let : IsCofibrant X := CellFamilySimplicialModel.isCofibrant_of_classicalCW X
  exact CellFamilySimplicialModel.toSingular_weak X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The boundary-family map is exactly the literal coproduct of boundary inclusions. -/
theorem boundarySum_eq (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    boundarySum X x P =
      CategoryTheory.Limits.Sigma.map (fun _ : P => (SSet.boundary.{u} 2).ι) := by
  rfl

/-- Every actual attaching leg is the original matched-boundary adjoint. -/
theorem attaching_ι (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) p ≫
        attaching X x P =
      sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
        ((SSet.boundary.toClassicalCellDiskArrowIso.{u} 2).hom.left ≫
          LoopCellAttachment.attachingMap X x P p) := by
  exact CellFamilySimplicialModel.attaching_ι X 1 P (LoopCellAttachment.attachingMap X x P) p

/-- Every actual characteristic leg is the original whole matched-disk adjoint. -/
theorem diskMates_ι (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫ diskMates X x P =
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        ((SSet.boundary.toClassicalCellDiskArrowIso.{u} 2).hom.right ≫
          LoopCellAttachment.cell X x P p) := by
  exact CellFamilySimplicialModel.diskMates_ι X 1 P (LoopCellAttachment.attachingMap X x P) p

/-- The realization comparison uses the same simplicial map and the actual original counit. -/
theorem realizationMap_eq (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    realizationMap X x P =
      SSet.toTop.map (toSingular X x P) ≫
        sSetTopAdj.counit.app (LoopCellAttachment.space X x P) := by
  exact CellFamilySimplicialModel.realizationMap_eq X 1 P (LoopCellAttachment.attachingMap X x P)

/-- The specialization is the same literal pushout of the original
loop boundary family and original attaching adjoints. -/
theorem model_eq_pushout (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    model X x P = pushout (boundarySum X x P) (attaching X x P) := by
  change pushout (CellFamilySimplicialModel.boundarySum 1 P)
      (CellFamilySimplicialModel.attaching X 1 P (LoopCellAttachment.attachingMap X x P)) = _
  rw [CellFamilySimplicialModel.boundarySum_eq]
  rfl

end AlgebraicTopology.LoopCellSimplicialModel

end
