/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkCell
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual marked coefficient pushouts of the original sharp interval

The original top cone coefficient already has every edge marked, since
all its original subset maxima are the top vertex. The root free legs
are the original whole self-path isomorphisms. At the positive interval
vertex both actual free root values are initial. These same original
maps prove the genuine marked pushout at every evaluation coefficient.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The entire original top cone coefficient already has its actual maximal marking because every original subset
maximum is the top vertex. -/
def coneSharpTopIso (n : ℕ) : coneWeight (⊤ : Vertex.{u} n) ≅ max (coneWeight (⊤ : Vertex.{u} n)).toSSet :=
  isoMk (Iso.refl _) (fun e => by
    change ((e.obj 0).maximum = (e.obj 1).maximum) ↔ True
    have h : ∀ a : ConeSubset (⊤ : Vertex.{u} n), a.maximum = ⊤ :=
      fun a => le_antisymm le_top (a.le_maximum ⊤ a.mem)
    exact ⟨fun _ => True.intro, fun _ => (h (e.obj 0)).trans (h (e.obj 1)).symm⟩)

/-- The top coefficient isomorphism retains precisely the unchanged original sharp coefficient map. -/
theorem coneSharpTopIso_hom (n : ℕ) :
    (coneSharpTopIso.{u} n).hom = (coneSharp n).app (op (SimplicialThickening.mk (⊤ : Vertex.{u} n))) := by
  apply Hom.ext
  rfl

/-- The same genuine sharp root free leg is its whole original marked self-path projection at the actual root. -/
theorem coneSharpRootFreeLeg_self :
    coneSharpRootFreeLeg.{u}.app (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} 1) (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet)).hom := by
  let e := coherentFreeSelfValueIso (⊥ : Vertex.{u} 1) (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet)
  apply (cancel_epi e.inv).mp
  exact coneSharpRootFreeLeg_unit.trans e.inv_hom_id.symm

/-- The unchanged whole sharp root free leg is a genuine marked isomorphism at its original root coefficient. -/
theorem coneSharpRootFreeLeg_isIso_self :
    IsIso (coneSharpRootFreeLeg.{u}.app (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))) :=
  coneSharpRootFreeLeg_self.symm ▸
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} 1) (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet)).isIso_hom

/-- Every positive original interval coefficient is the actual top coefficient, so its unchanged sharp map is
genuinely an isomorphism. -/
theorem coneSharpInterval_positive_isIso (i : Vertex.{u} 1) (hi : (⊥ : Vertex.{u} 1) < i) :
    IsIso ((coneSharp 1).app (op (SimplicialThickening.mk i))) := by
  have htop : i = (⊤ : Vertex.{u} 1) := by
    apply ULift.ext
    apply Fin.ext
    have hlt : 0 < i.down.val := hi
    have hbound := i.down.isLt
    change i.down.val = 1
    omega
  subst i
  exact (coneSharpTopIso_hom 1).symm ▸ (coneSharpTopIso 1).isIso_hom

/-- The original whole sharp interval cell square at each actual marked evaluation coefficient. -/
def coneSharpRootMarkComponentCocone (i : Vertex.{u} 1) :
    PushoutCocone (coneSharpRootMarkFreeMap.app (op (SimplicialThickening.mk i)))
      ((coneRootFreeMap 1).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk (coneSharpRootFreeLeg.app (op (SimplicialThickening.mk i)))
    ((coneSharp 1).app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) coneSharpRootMark_condition)

/-- Each full original marked interval coefficient is the genuine pushout of the same root marking cell and original
enriched free legs. -/
def coneSharpRootMarkComponentIsColimit (i : Vertex.{u} 1) : IsColimit (coneSharpRootMarkComponentCocone i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} 1 := ⊥
  let f := coneSharpRootMarkFreeMap.app c
  let g := (coneRootFreeMap 1).app c
  let l := coneSharpRootFreeLeg.app c
  let r := (coneSharp 1).app c
  have hw : CommSq f g l r := ⟨congrArg (fun a => a.app c) coneSharpRootMark_condition⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let hA := coherentFreeBeyondIsInitial hi (coneWeight root)
      let hD := coherentFreeBeyondIsInitial hi (max (coneWeight root).toSSet)
      let e := hA.uniqueUpToIso hD
      have he : f = e.hom := hA.hom_ext _ _
      have : IsIso f := he.symm ▸ e.isIso_hom
      have : IsIso r := coneSharpInterval_positive_isIso i hi
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      have : IsIso g := coneRootFreeMap_isIso_self 1
      have : IsIso l := coneSharpRootFreeLeg_isIso_self
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

end SSet.Marked.CoherentWeight
