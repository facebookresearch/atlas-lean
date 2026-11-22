/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathMappingFibreTarget
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathLeadingEdgeFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PullbackFibreWeakDetection

/-!
# The genuine weak row-point comparison of original Segal path fibres

The entire original leading-edge row comparison is weak over the same
full tail base. Both original projections are actual Kan fibrations.
The original fibrewise weak-equivalence theorem proves weakness of each
whole prescribed-tail fibre comparison, and the actual target pasting
isomorphism retains its original mapping fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.LeftDecalageObject

/-- The actual leading-edge row map on the fibre at the same prescribed whole tail simplex. -/
def rowPointLeadingComparison (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointFibre W x n b ⟶ leadingEdgePointTarget W x n b :=
  pullback.map _ _ _ _ (leadingEdgeComparison W x n) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (leadingEdgeComparison_tail W x n).symm)
    (by simp)

/-- The original whole row-point leading-edge comparison is genuinely weak at an original Segal space. -/
theorem rowPointLeadingComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    SSet.realizationWeakEquivalences (rowPointLeadingComparison W x n b) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ := projection_fibration W x hW.1 n
  let _ := InitialEdgeTailMapping.sourceEdgeTarget_tail_fibration W x hW.1 n
  exact ((SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (leadingEdgeComparison W x n) ((projection W x).app (op (SimplexCategory.mk n)))
    (pullback.snd (sourceEdgesTarget W x) (InitialEdgeTailMapping.tailFirstVertex W n))
    (leadingEdgeComparison_tail W x n)).mp (leadingEdgeComparison_weak W hW x n)) b

/-- The whole original path fibre maps weakly to the original mapping fibre at its same prescribed endpoints. -/
theorem rowPointLeadingMappingComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    SSet.realizationWeakEquivalences
      (rowPointLeadingComparison W x n b ≫ (leadingEdgePointTargetIso W x n b).hom) :=
  SSet.realizationWeakEquivalences.comp_mem _ _ (rowPointLeadingComparison_weak W hW x n b)
    (SSet.realizationWeakEquivalences.of_isIso _)

set_option backward.isDefEq.respectTransparency false in
/-- The whole weak path-fibre comparison is precisely the original leading-edge mapping-fibre map. -/
theorem rowPointLeadingComparison_eq_mapping (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointLeadingComparison W x n b ≫ (leadingEdgePointTargetIso W x n b).hom =
      rowPointMappingComparison W x n b := by
  apply pullback.hom_ext
  · rw [Category.assoc, leadingEdgePointTargetIso_edge]
    have hp : rowPointLeadingComparison W x n b ≫ pullback.fst _ _ =
        pullback.fst ((projection W x).app (op (SimplexCategory.mk n))) b ≫ leadingEdgeComparison W x n :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc (rowPointLeadingComparison W x n b), hp]
    simp only [Category.assoc]
    rw [leadingEdgeComparison_edge]
    exact (pullback.lift_fst _ _ _).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The actual original leading-edge mapping-fibre comparison is weak at every whole prescribed tail. -/
theorem rowPointMappingComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    SSet.realizationWeakEquivalences (rowPointMappingComparison W x n b) := by
  rw [← rowPointLeadingComparison_eq_mapping]
  exact rowPointLeadingMappingComparison_weak W hW x n b

end SimplicialSpace.LeftDecalageObject
