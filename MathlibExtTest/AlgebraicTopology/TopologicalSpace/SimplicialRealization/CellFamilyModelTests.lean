/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CellFamilyFundamentalGroupoid
import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSimplicialModel

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology Topology.CWComplex
  HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

universe u

#check @CellFamilySimplicialModel.toSingular_weak
#print axioms CellFamilySimplicialModel.toSingular_weak
#check @CellFamilySimplicialModel.realizationMap_disk
#print axioms CellFamilySimplicialModel.realizationMap_disk
#check @CellFamilySimplicialModel.isCofibrant_attachment
#print axioms CellFamilySimplicialModel.isCofibrant_attachment
#check @CellFamilySimplicialModel.inclusionFundamentalGroupoid_isEquivalence
#print axioms CellFamilySimplicialModel.inclusionFundamentalGroupoid_isEquivalence
#check @LoopCellSimplicialModel.model_eq_pushout
#print axioms LoopCellSimplicialModel.model_eq_pushout

/-- Every whole original closed disk is retained for arbitrary dimension,
including infinite or empty index families, without an expected comparison. -/
theorem client_all_dimensions_and_cells (X : TopCat.{u}) (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) (i : I) :
    SSet.toTop.map (Sigma.ι (fun _ : I => (Δ[n + 1] : SSet.{u})) i ≫
        CellFamilySimplicialModel.newDisks X n I att) ≫
      CellFamilySimplicialModel.realizationMap X n I att =
        (SSet.boundary.toClassicalCellDiskArrowIso (n + 1)).hom.right ≫
          CellFamilyAttachment.cell X n att i :=
  CellFamilySimplicialModel.realizationMap_disk X n I att i

/-- Actual higher-cell inclusions preserve all original fundamental-groupoid
components; no groupoid equivalence is given as an input. -/
theorem client_actual_three_cell_groupoid (X : TopCat.{u}) [IsCofibrant X] (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} 3).snd ⟶ X)) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map (CellFamilyAttachment.inclusion X 2
      att))).IsEquivalence :=
  CellFamilySimplicialModel.inclusionFundamentalGroupoid_isEquivalence X 2 (by decide) I att

/-- The original loop specialization keeps the exact ordinary pushout data. -/
theorem client_original_loop_pushout (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    LoopCellSimplicialModel.model X x P = pushout
      (LoopCellSimplicialModel.boundarySum X x P) (LoopCellSimplicialModel.attaching X x P) :=
  LoopCellSimplicialModel.model_eq_pushout X x P

/-- The same actual first attachment, rather than a supplied new CW model,
derives the cofibrancy needed for the next three-cell pushout. -/
theorem client_cofibrancy_of_actual_attachment (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    IsCofibrant (CellFamilyAttachment.space X n att) := by
  let := CellFamilySimplicialModel.isCofibrant_of_classicalCW X
  exact CellFamilySimplicialModel.isCofibrant_attachment X n I att

end
