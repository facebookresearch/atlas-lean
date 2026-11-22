/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentFreeEmptyValue
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Genuine original marked evaluation pushouts of the entire root horn

At root the original free leg is the SAME actual whole self-path
projection isomorphism. Above root both original root-free sources are
genuinely initial and the supported inclusion is the entire original
marked coefficient isomorphism. These actual maps give the full marked
pushout at every original coefficient, retaining all scalar degrees.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The SAME entire original root-horn free leg is its actual original whole self-path projection. -/
theorem coneRootHornFreeLeg_self {n : ℕ} (k : Fin (n + 2)) :
    (coneRootHornFreeLeg.{u} k).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 1))
        (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)))).hom := by
  apply (cancel_epi (coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 1))
    (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)))).inv).mp
  exact (coneRootHornFreeLeg_unit k).trans
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 1))
      (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)))).inv_hom_id.symm

/-- The actual original entire root-horn free leg is a genuine marked isomorphism at its original root. -/
theorem coneRootHornFreeLeg_isIso_self {n : ℕ} (k : Fin (n + 2)) :
    IsIso ((coneRootHornFreeLeg.{u} k).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) :=
  (coneRootHornFreeLeg_self k).symm ▸
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 1))
      (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)))).isIso_hom

/-- The SAME original complete root-horn free-cell square at every original marked coefficient. -/
def coneRootHornComponentCocone {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    PushoutCocone ((coneRootHornCellFreeMap k).app (op (SimplicialThickening.mk i)))
      ((coneRootHornFreeLeg k).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneRootFreeMap (n + 1)).app (op (SimplicialThickening.mk i)))
    ((coneRootHornDiagramInclusion k).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneRootHornCell_condition k))

/-- Every SAME original marked coefficient is the actual pushout of its unchanged complete original root-horn
free-cell square. -/
def coneRootHornComponentIsColimit {n : ℕ} (k : Fin (n + 2)) (i : Vertex.{u} (n + 1)) :
    IsColimit (coneRootHornComponentCocone k i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} (n + 1) := ⊥
  let f := (coneRootHornCellFreeMap k).app c
  let g := (coneRootHornFreeLeg k).app c
  let l := (coneRootFreeMap (n + 1)).app c
  let r := (coneRootHornDiagramInclusion k).app c
  have hw : CommSq f g l r := ⟨congrArg (fun a => a.app c) (coneRootHornCell_condition k)⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let hA := coherentFreeBeyondIsInitial hi (coneRootHornMarked k root)
      let hD := coherentFreeBeyondIsInitial hi (coneWeight root)
      let e := hA.uniqueUpToIso hD
      have he : f = e.hom := hA.hom_ext _ _
      let _ : IsIso f := he.symm ▸ e.isIso_hom
      have hr : IsIso (coneRootHornInclusion k i) :=
        (coneRootHornAboveIso_hom k hi) ▸ (coneRootHornAboveIso k hi).isIso_hom
      let _ : IsIso r := hr
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      let _ : IsIso g := coneRootHornFreeLeg_isIso_self k
      let _ : IsIso l := coneRootFreeMap_isIso_self (n + 1)
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

end SSet.Marked.CoherentWeight
