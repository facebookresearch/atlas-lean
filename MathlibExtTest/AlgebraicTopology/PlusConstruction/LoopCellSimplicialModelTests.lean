/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSimplicialModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
import MathlibExt.AlgebraicTopology.SingularHomology.Integral

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology Topology.CWComplex
open AlgebraicTopology.LoopCellSimplicialModel
open scoped Simplicial

universe u

#check @AlgebraicTopology.LoopCellSimplicialModel.isPushout
#print axioms AlgebraicTopology.LoopCellSimplicialModel.isPushout
#check @AlgebraicTopology.LoopCellSimplicialModel.adjunctSquare
#print axioms AlgebraicTopology.LoopCellSimplicialModel.adjunctSquare
#check @AlgebraicTopology.LoopCellSimplicialModel.realizationMap_disk
#print axioms AlgebraicTopology.LoopCellSimplicialModel.realizationMap_disk
#check @AlgebraicTopology.LoopCellSimplicialModel.oldInclusion_mono
#print axioms AlgebraicTopology.LoopCellSimplicialModel.oldInclusion_mono
#check @AlgebraicTopology.LoopCellSimplicialModel.realizationMap_weak
#print axioms AlgebraicTopology.LoopCellSimplicialModel.realizationMap_weak
#check @AlgebraicTopology.LoopCellSimplicialModel.toSingular_weak
#print axioms AlgebraicTopology.LoopCellSimplicialModel.toSingular_weak

/-- Every actual old realization point retains the original inclusion after the original counit. -/
private theorem client_actual_original_space_values
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))
    (z : SSet.toTop.obj (TopCat.toSSet.obj X)) :
    realizationMap X x P (SSet.toTop.map (oldInclusion X x P) z) =
      LoopCellAttachment.inclusion X x P (sSetTopAdj.counit.app X z) :=
  ConcreteCategory.congr_hom (realizationMap_old X x P) z

/-- Every point of the entire actual classical closed disk retains its original characteristic map.
  -/
private theorem client_entire_original_classical_disk
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P)
    (q : (classicalCellDiskPair.{u} 2).fst) :
    realizationMap X x P
        (SSet.toTop.map (CategoryTheory.Limits.Sigma.ι
          (fun _ : P => (Δ[2] : SSet.{u})) p ≫ newDisks X x P)
          ((SSet.boundary.toClassicalCellDiskArrowIso 2).inv.right q)) =
      LoopCellAttachment.cell X x P p q := by
  let e := Arrow.rightFunc.mapIso (SSet.boundary.toClassicalCellDiskArrowIso 2)
  have h := ConcreteCategory.congr_hom (realizationMap_disk X x P p) (e.inv q)
  have hi : e.hom (e.inv q) = q := ConcreteCategory.congr_hom e.inv_hom_id q
  exact h.trans (congrArg (LoopCellAttachment.cell X x P p) hi)

/-- The same original comparison induces the actual integral-chain quasi-isomorphism. -/
private theorem client_actual_original_integral_chains
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    (x : X) (P : Subgroup (FundamentalGroup X x)) :
    QuasiIso (SSet.chainComplexMap (toSingular X x P)
      (singularIntegralCoefficients : AddCommGrpCat.{u})) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp
    (toSingular_weak X x P) (singularIntegralCoefficients : AddCommGrpCat.{u})

#check @AlgebraicTopology.LoopCellSimplicialModel.boundarySum_eq
#print axioms AlgebraicTopology.LoopCellSimplicialModel.boundarySum_eq
#check @AlgebraicTopology.LoopCellSimplicialModel.attaching_ι
#print axioms AlgebraicTopology.LoopCellSimplicialModel.attaching_ι
#check @AlgebraicTopology.LoopCellSimplicialModel.diskMates_ι
#print axioms AlgebraicTopology.LoopCellSimplicialModel.diskMates_ι
#check @AlgebraicTopology.LoopCellSimplicialModel.realizationMap_eq
#print axioms AlgebraicTopology.LoopCellSimplicialModel.realizationMap_eq

/-- The original simplicial disk inclusion retains its whole actual adjoint through the model. -/
private theorem client_actual_model_disk_adjoint
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
        newDisks X x P) ≫ toSingular X x P =
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        ((SSet.boundary.toClassicalCellDiskArrowIso.{u} 2).hom.right ≫
          LoopCellAttachment.cell X x P p) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => CategoryTheory.Limits.Sigma.ι
      (fun _ : P => (Δ[2] : SSet.{u})) p ≫ f) (toSingular_disks X x P)).trans
        (diskMates_ι X x P p))

/-- The actual monomorphism used for the pulled cell pushout is derived from its literal recipe. -/
private theorem client_actual_boundary_family_mono
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    Mono (boundarySum X x P) := by
  have h : Mono (CategoryTheory.Limits.Sigma.map
      (fun _ : P => (SSet.boundary.{u} 2).ι)) := inferInstance
  exact Eq.mp (congrArg (fun f : boundaries X x P ⟶ disks X x P => Mono f)
    (boundarySum_eq X x P).symm) h

end
