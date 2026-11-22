/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentFreeEmptyValue
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual marked evaluation pushouts of the complete root boundary

At the original root the complete boundary free leg is its genuine
self-path projection isomorphism. At every positive vertex both root
free sources are genuinely initial and the supported inclusion is the
whole original marked isomorphism. These actual maps give the marked
pushout at every original coefficient and in every scalar degree.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original root-boundary free leg is the whole native self-path projection. -/
theorem coneRootBoundaryFreeLeg_self (n : ℕ) :
    (coneRootBoundaryFreeLeg.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
        (coneRootBoundaryMarked (⊥ : Vertex.{u} n))).hom := by
  apply (cancel_epi (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
    (coneRootBoundaryMarked (⊥ : Vertex.{u} n))).inv).mp
  exact (coneRootBoundaryFreeLeg_unit n).trans
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
      (coneRootBoundaryMarked (⊥ : Vertex.{u} n))).inv_hom_id.symm

/-- The unchanged whole root-boundary free leg is a genuine marked isomorphism at the root. -/
theorem coneRootBoundaryFreeLeg_isIso_self (n : ℕ) :
    IsIso ((coneRootBoundaryFreeLeg.{u} n).app
      (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) :=
  (coneRootBoundaryFreeLeg_self n).symm ▸
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
      (coneRootBoundaryMarked (⊥ : Vertex.{u} n))).isIso_hom

/-- The actual full coordinate-boundary free-cell square at every original coefficient. -/
def coneRootBoundaryComponentCocone (n : ℕ) (i : Vertex.{u} n) :
    PushoutCocone ((coneRootBoundaryCellFreeMap n).app (op (SimplicialThickening.mk i)))
      ((coneRootBoundaryFreeLeg n).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneRootFreeMap n).app (op (SimplicialThickening.mk i)))
    ((coneRootBoundaryDiagramInclusion n).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneRootBoundaryCell_condition n))

/-- Every original marked coefficient is the genuine pushout of its same complete root-boundary cell. -/
def coneRootBoundaryComponentIsColimit (n : ℕ) (i : Vertex.{u} n) :
    IsColimit (coneRootBoundaryComponentCocone n i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} n := ⊥
  let f := (coneRootBoundaryCellFreeMap n).app c
  let g := (coneRootBoundaryFreeLeg n).app c
  let l := (coneRootFreeMap n).app c
  let r := (coneRootBoundaryDiagramInclusion n).app c
  have hw : CommSq f g l r := ⟨congrArg (fun a => a.app c) (coneRootBoundaryCell_condition n)⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let hA := coherentFreeBeyondIsInitial hi (coneRootBoundaryMarked root)
      let hD := coherentFreeBeyondIsInitial hi (coneWeight root)
      let e := hA.uniqueUpToIso hD
      have he : f = e.hom := hA.hom_ext _ _
      let _ : IsIso f := he.symm ▸ e.isIso_hom
      have hr : IsIso (coneRootBoundaryInclusion i) :=
        (coneRootBoundaryAboveIso_hom hi) ▸ (coneRootBoundaryAboveIso hi).isIso_hom
      let _ : IsIso r := hr
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      let _ : IsIso g := coneRootBoundaryFreeLeg_isIso_self n
      let _ : IsIso l := coneRootFreeMap_isIso_self n
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

end SSet.Marked.CoherentWeight
