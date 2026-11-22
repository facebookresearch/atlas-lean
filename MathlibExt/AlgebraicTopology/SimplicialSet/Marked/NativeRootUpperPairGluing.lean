/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinatePairs
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterMonomorphism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUpperRootInverseUnit

/-!
# Genuine inverse gluing on all original upper/upper root intersections

Both original upper coordinates enter the same original positive root
cone through their unchanged full marked maps. The original positive
inclusion detects their equality on each entire original intersection.
The same actual native positive section therefore gives equal upper
inverse maps, including all diagonal and ordered/swapped coordinates.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Both original native upper inverse maps agree on every full marked upper/upper root intersection through the
same actual original positive entry and native section. -/
theorem nativeRootUpperPair_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (j k : Fin (n + 2)) (hj : 0 < j) (hk : 0 < k) :
    coneRootCoordinatePairLeft n (coneRootUpperIndex n j hj) (coneRootUpperIndex n k hk) ≫
      nativeUpperRootBoundaryInverse B σ j hj =
      coneRootCoordinatePairRight n (coneRootUpperIndex n j hj) (coneRootUpperIndex n k hk) ≫
        nativeUpperRootBoundaryInverse B σ k hk := by
  let a := coneRootUpperIndex.{u} n j hj
  let b := coneRootUpperIndex.{u} n k hk
  let l := coneRootCoordinatePairLeft n a b
  let r := coneRootCoordinatePairRight n a b
  let v := coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩
  let w := coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up k, hk⟩
  let ι := coneAfterInclusion (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
  let P := (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
  have ha : l ≫ v = r ≫ w := by
    apply (cancel_mono ι).mp
    have hl : (l ≫ v) ≫ ι = coneRootCoordinatePairInclusion n a b :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => l ≫ f) (coneUpperFaceToAfter_inclusion (⊥ : Vertex.{u} (n + 1))
          (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩)).trans (coneRootCoordinatePairLeft_inclusion n a b))
    have hr : (r ≫ w) ≫ ι = coneRootCoordinatePairInclusion n a b :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => r ≫ f) (coneUpperFaceToAfter_inclusion (⊥ : Vertex.{u} (n + 1))
          (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up k, hk⟩)).trans (coneRootCoordinatePairRight_inclusion n a b))
    exact hl.trans hr.symm
  exact (Category.assoc l v P).symm.trans ((congrArg (fun f => f ≫ P) ha).trans (Category.assoc r w P))

end SSet.Marked
