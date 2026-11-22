/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryPositiveSquare
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryAfterAbove

/-!
# Actual original positive/free-root marked evaluation pushouts

At the original root both actual free legs are their genuine original
self-path projection isomorphisms. At each positive vertex both free
root values are genuinely initial and the original positive inclusion
is the whole marked supported-coefficient isomorphism. These same
maps give the full original marked pushout at every coefficient.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual full positive free leg at the original root is precisely the genuine whole marked self-path
projection. -/
theorem conePositiveRootFreeLeg_self (n : ℕ) :
    (conePositiveRootFreeLeg.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
        (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n))).hom := by
  let e := coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n))
  apply (cancel_epi e.inv).mp
  exact (conePositiveRootFreeLeg_unit n).trans e.inv_hom_id.symm

/-- The unchanged original positive free leg is a genuine marked isomorphism at the actual root. -/
theorem conePositiveRootFreeLeg_isIso_self (n : ℕ) :
    IsIso ((conePositiveRootFreeLeg.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) :=
  (conePositiveRootFreeLeg_self n).symm ▸
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n))).isIso_hom

/-- The full actual original positive/free-root square at every original marked evaluation coefficient. -/
def coneRootBoundaryPositiveComponentCocone (n : ℕ) (i : Vertex.{u} n) :
    PushoutCocone ((conePositiveBoundaryFreeMap n).app (op (SimplicialThickening.mk i)))
      ((conePositiveRootFreeLeg n).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneRootBoundaryFreeLeg n).app (op (SimplicialThickening.mk i)))
    ((coneRootBoundaryAfterMap n).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneRootBoundaryPositive_condition n))

/-- Each unchanged original marked coefficient is the actual full pushout of its same original positive/free-root
maps. -/
def coneRootBoundaryPositiveComponentIsColimit (n : ℕ) (i : Vertex.{u} n) :
    IsColimit (coneRootBoundaryPositiveComponentCocone n i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} n := ⊥
  let f := (conePositiveBoundaryFreeMap n).app c
  let g := (conePositiveRootFreeLeg n).app c
  let l := (coneRootBoundaryFreeLeg n).app c
  let r := (coneRootBoundaryAfterMap n).app c
  have hw : CommSq f g l r := ⟨congrArg (fun a => a.app c) (coneRootBoundaryPositive_condition n)⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let hA := coherentFreeBeyondIsInitial hi (coneAfterWeight root root)
      let hB := coherentFreeBeyondIsInitial hi (coneRootBoundaryMarked root)
      let e := hA.uniqueUpToIso hB
      have he : f = e.hom := hA.hom_ext _ _
      have : IsIso f := he.symm ▸ e.isIso_hom
      have hr : IsIso (coneRootBoundaryAfterInclusion i) :=
        (coneRootBoundaryAfterAboveIso_hom hi) ▸ (coneRootBoundaryAfterAboveIso hi).isIso_hom
      have : IsIso r := hr
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      have : IsIso g := conePositiveRootFreeLeg_isIso_self n
      have : IsIso l := coneRootBoundaryFreeLeg_isIso_self n
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

end SSet.Marked.CoherentWeight
