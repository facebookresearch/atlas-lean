/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootValueIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Genuine original root-cell marked attachment values

At the original root both actual free identity components are native
self-value isomorphisms. At larger original vertices both actual free
root sources are initial and the upper inclusion is the whole original
marked isomorphism. These original maps prove a true marked pushout in
every coefficient, including the zero-dimensional case.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original root free-cell square at every full original coefficient. -/
def coneRootCellComponentCocone (n : ℕ) (i : Vertex.{u} n) :
    PushoutCocone ((coneRootBoundaryFreeMap n).app (op (SimplicialThickening.mk i)))
      ((coneAfterRootFreeMap n).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneRootFreeMap n).app (op (SimplicialThickening.mk i)))
    ((coneAfterDiagramInclusion (⊥ : Vertex.{u} n)).app (op (SimplicialThickening.mk i)))
    (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneRootCell_condition n))

/-- Every original whole marked coefficient has its genuine root attachment pushout, with no value-colimit
  outcome premise. -/
def coneRootCellComponentIsColimit (n : ℕ) (i : Vertex.{u} n) :
    IsColimit (coneRootCellComponentCocone n i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} n := ⊥
  let f := (coneRootBoundaryFreeMap n).app c
  let g := (coneAfterRootFreeMap n).app c
  let l := (coneRootFreeMap n).app c
  let r := (coneAfterDiagramInclusion root).app c
  have hw : CommSq f g l r := ⟨congrArg (fun a => a.app c) (coneRootCell_condition n)⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let hA := coherentFreeBeyondIsInitial hi (coneAfterWeight root root)
      let hD := coherentFreeBeyondIsInitial hi (coneWeight root)
      let e := hA.uniqueUpToIso hD
      have he : f = e.hom := hA.hom_ext _ _
      let _ : IsIso f := he.symm ▸ e.isIso_hom
      have hr : IsIso (coneAfterInclusion i root) :=
        (coneAfterAboveIso_hom hi) ▸ (coneAfterAboveIso hi).isIso_hom
      let _ : IsIso r := hr
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      let _ : IsIso g := coneAfterRootFreeMap_isIso_self n
      let _ : IsIso l := coneRootFreeMap_isIso_self n
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

end SSet.Marked.CoherentWeight
