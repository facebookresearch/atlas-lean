/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingReflection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# The actual marking pushout of one original edge

The minimally marked original carrier gains exactly its supplied edge
and the original degeneracies by pushing out the actual interval marking
cell along that edge's whole Yoneda map. The universal marked map keeps
the original simplicial map on every degree. No weak class is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original edge supplies its entire minimally marked interval map. -/
def selectedEdgeMinimalMap (X : SSet.{u}) (e : X _⦋1⦌) :
    min (Δ[1] : SSet.{u}) ⟶ min X := minimal.map (SSet.yonedaEquiv.symm e)

/-- The whole original carrier is included with its new selected edge. -/
def selectedEdgeMinimalLeg (X : SSet.{u}) (e : X _⦋1⦌) :
    min X ⟶ withEdges X {e} := ofMin (𝟙 X)

/-- The same marked original edge gives its entire maximally marked interval leg. -/
def selectedEdgeSharpLeg (X : SSet.{u}) (e : X _⦋1⦌) :
    max (Δ[1] : SSet.{u}) ⟶ withEdges X {e} := intervalMapOfMarkedEdge e (Or.inr rfl)

/-- The square preserves the full original Yoneda edge and carrier identity. -/
theorem selectedEdgeMarking_condition (X : SSet.{u}) (e : X _⦋1⦌) :
    edgeMarkCell ≫ selectedEdgeSharpLeg X e =
      selectedEdgeMinimalMap X e ≫ selectedEdgeMinimalLeg X e := by
  apply Hom.ext
  change 𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e =
    SSet.yonedaEquiv.symm e ≫ 𝟙 X
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The specified original carrier and selected edge form the genuine marking cocone. -/
def selectedEdgeMarkingCocone (X : SSet.{u}) (e : X _⦋1⦌) :
    PushoutCocone edgeMarkCell (selectedEdgeMinimalMap X e) :=
  PushoutCocone.mk (selectedEdgeSharpLeg X e) (selectedEdgeMinimalLeg X e)
    (selectedEdgeMarking_condition X e)

/-- Every competing cocone marks precisely the same original edge image. -/
theorem selectedEdgeCocone_marks (X : SSet.{u}) (e : X _⦋1⦌)
    (s : PushoutCocone edgeMarkCell (selectedEdgeMinimalMap X e)) :
    s.inr.hom.app (op ⦋1⦌) e ∈ s.pt.marking := by
  have h := congrArg
    (fun f => f.app (op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
      (congrArg Hom.hom s.condition)
  change s.inl.hom.app (op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
    s.inr.hom.app (op ⦋1⦌)
      ((SSet.yonedaEquiv.symm e).app (op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))) at h
  rw [SSet.yonedaEquiv_symm_app_id] at h
  exact h ▸ s.inl.preserve (Set.mem_univ _)

/-- The actual universal map keeps the whole original carrier map of the cocone. -/
def selectedEdgeMarkingDesc (X : SSet.{u}) (e : X _⦋1⦌)
    (s : PushoutCocone edgeMarkCell (selectedEdgeMinimalMap X e)) :
    withEdges X {e} ⟶ s.pt := ofWithEdges s.inr.hom (by
  intro a ha
  have ha' : a = e := ha
  rw [ha']
  exact selectedEdgeCocone_marks X e s)

/-- The universal marked map retains every degree of the original simplicial map. -/
theorem selectedEdgeMarkingDesc_hom (X : SSet.{u}) (e : X _⦋1⦌)
    (s : PushoutCocone edgeMarkCell (selectedEdgeMinimalMap X e)) :
    (selectedEdgeMarkingDesc X e s).hom = s.inr.hom := rfl

/-- The original selected-edge carrier is the actual full marked pushout. -/
def selectedEdgeMarkingIsColimit (X : SSet.{u}) (e : X _⦋1⦌) :
    IsColimit (selectedEdgeMarkingCocone X e) := by
  refine PushoutCocone.IsColimit.mk (selectedEdgeMarking_condition X e)
    (selectedEdgeMarkingDesc X e) ?_ ?_ ?_
  · intro s
    apply Hom.ext
    change SSet.yonedaEquiv.symm e ≫ s.inr.hom = s.inl.hom
    exact (congrArg Hom.hom s.condition).symm.trans (Category.id_comp _)
  · intro s
    exact Hom.ext (Category.id_comp _)
  · intro s m _ hm
    apply Hom.ext
    change m.hom = s.inr.hom
    have h : 𝟙 X ≫ m.hom = s.inr.hom := congrArg Hom.hom hm
    exact (Category.id_comp m.hom).symm.trans h

/-- The same original marking square is a categorical pushout on its full marked carriers. -/
theorem selectedEdgeMarking_isPushout (X : SSet.{u}) (e : X _⦋1⦌) :
    IsPushout edgeMarkCell (selectedEdgeMinimalMap X e)
      (selectedEdgeSharpLeg X e) (selectedEdgeMinimalLeg X e) :=
  IsPushout.of_isColimit (selectedEdgeMarkingIsColimit X e)

end SSet.Marked
