/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalHornFreeCell

/-!
# Every original critical free-root coefficient is a genuine marked pushout

At the original root both exact original free legs are their whole
marked self-path projection isomorphisms. Above root both original
root-free values are genuinely initial and the complete supported
critical coefficient inclusion is its same whole marked isomorphism.
These original maps give an actual marked pushout at every coefficient.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The same entire original supported critical horn free leg at root is precisely the genuine whole marked
self-path projection. -/
theorem coneCriticalHornFreeLeg_self (n : ℕ) :
    (coneCriticalHornFreeLeg.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 2)) (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2)))).hom := by
  let e := coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 2)) (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2)))
  apply (cancel_epi e.inv).mp
  exact (coneCriticalHornFreeLeg_unit n).trans e.inv_hom_id.symm

/-- The same complete original critical target free leg at root is the genuine whole marked self-path projection. -/
theorem coneCriticalRootFreeLeg_self (n : ℕ) :
    (coneCriticalRootFreeLeg.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 2)) (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom := by
  let e := coherentFreeSelfValueIso (⊥ : Vertex.{u} (n + 2)) (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))
  apply (cancel_epi e.inv).mp
  exact (coneCriticalRootFreeLeg_unit n).trans e.inv_hom_id.symm

/-- The SAME entire original critical free-root square at every full marked evaluation coefficient. -/
def coneCriticalHornComponentCocone (n : ℕ) (i : Vertex.{u} (n + 2)) :
    PushoutCocone ((coneCriticalHornCellFreeMap n).app (op (SimplicialThickening.mk i)))
      ((coneCriticalHornFreeLeg n).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk ((coneCriticalRootFreeLeg n).app (op (SimplicialThickening.mk i)))
    ((coneCriticalHornInclusion n).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) (coneCriticalHornCell_condition n))

/-- Every entire original critical coefficient is the actual marked pushout of its SAME original full free-root maps. -/
def coneCriticalHornComponentIsColimit (n : ℕ) (i : Vertex.{u} (n + 2)) :
    IsColimit (coneCriticalHornComponentCocone n i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} (n + 2) := ⊥
  let f := (coneCriticalHornCellFreeMap n).app c
  let g := (coneCriticalHornFreeLeg n).app c
  let l := (coneCriticalRootFreeLeg n).app c
  let r := (coneCriticalHornInclusion n).app c
  have hw : CommSq f g l r := ⟨congrArg (fun a => a.app c) (coneCriticalHornCell_condition n)⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let hA := coherentFreeBeyondIsInitial hi (coneCriticalHornWeight n root)
      let hB := coherentFreeBeyondIsInitial hi (coneCriticalWeight n root)
      let e := hA.uniqueUpToIso hB
      have he : f = e.hom := hA.hom_ext _ _
      let _ : IsIso f := he.symm ▸ e.isIso_hom
      let _ : IsIso r := Eq.mp (congrArg (fun f => IsIso f) (coneCriticalHornAboveIso_hom n hi))
        (coneCriticalHornAboveIso n hi).isIso_hom
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      let _ : IsIso g := Eq.mp (congrArg (fun f => IsIso f) (coneCriticalHornFreeLeg_self n).symm)
        (coherentFreeSelfValueIso root (coneCriticalHornWeight n root)).isIso_hom
      let _ : IsIso l := Eq.mp (congrArg (fun f => IsIso f) (coneCriticalRootFreeLeg_self n).symm)
        (coherentFreeSelfValueIso root (coneCriticalWeight n root)).isIso_hom
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

end SSet.Marked.CoherentWeight
