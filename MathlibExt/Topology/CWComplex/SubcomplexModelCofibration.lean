/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.ClassicalRelativeCellComplex
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Model cofibrations from the actual classical relative CW presentation

The original subcomplex inclusion is the returned canonical relative CW cell
complex. Each complete boundary generator is transported to the actual realized
simplex boundary, and the existing transfinite lifting calculus supplies its
left lifting property. No homotopy extension or chosen lift is an input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
namespace Topology.CWComplex

/-- The literal inclusion of any classical subcomplex of the original Hausdorff
CW space belongs to the selected realized-boundary left lifting class. -/
theorem subcomplexInclusion_mem_realizedBoundaryLLP (X : TopCat.{u})
    [T2Space X] [CWComplex (Set.univ : Set X)]
    (A : Subcomplex (Set.univ : Set X)) :
    TopCat.realizedBoundaryInclusions.rlp.llp (subcomplexInclusion A) := by
  let c := classicalSubcomplexRelativeCWComplex X A
  let r : RelativeCellComplex.{u}
      (fun (n : ℕ) (_ : Unit) => SSet.toTop.map (SSet.boundary.{u} n).ι)
      (subcomplexInclusion A) :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
      attachCells := fun n hn =>
        (c.attachCells n hn).reindexCellTypes
          (fun _ : Unit => SSet.toTop.map (SSet.boundary.{u} n).ι) id
          (fun _ => (SSet.boundary.toTopDiskArrowIso.{u} n).symm) }
  let h := r.transfiniteCompositionOfShape'
    (I := TopCat.realizedBoundaryInclusions)
    (fun s => TopCat.boundary_mem_realizedBoundaryInclusions s.j)
  exact (MorphismProperty.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
    TopCat.realizedBoundaryInclusions ℕ) _ h.mem

end Topology.CWComplex
