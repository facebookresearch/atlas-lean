/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundarySupport
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# Whole original root-boundary marked enriched diagram

Original cone path action restricts to the actual coordinate boundary
at the root and whole cone coefficients above it. The restricted
action keeps every original path, scalar word and maximum mark.
Original identity and composition laws give the full enriched
diagram and its same original inclusion in the cone.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original whole path action restricts to the same actual root-boundary supports and markings. -/
def coneRootBoundaryAction {n : ℕ} (i j : Vertex.{u} n) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneRootBoundaryMarked j) ⟶ coneRootBoundaryMarked i where
  hom :=
    { app q := ↾fun x => ⟨(coneAction i j).hom.app q (x.1, x.2.val),
        coneRootBoundarySupport_action_mem i j q x.1 x.2.val x.2.property⟩
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact congr($((coneAction i j).hom.naturality f) (x.1, x.2.val)) }
  preserve {e} he := (coneAction i j).preserve (show
    (e.1, e.2.val) ∈ (prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j)).marking from
      ⟨he.1, he.2⟩)

/-- The complete original supported coefficients and path actions form the whole marked enriched root-boundary
diagram. -/
def coneRootBoundaryDiagram (n : ℕ) : EnrichedDiagram (Index.{u} n)ᵒᵖ where
  obj i := coneRootBoundaryMarked i.unop.as
  map i j := maxCurry (coneRootBoundaryAction j.unop.as i.unop.as)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ConeSubset.prepend_id _) (fun _ _ _ => Subsingleton.elim _ _)
  map_comp i j k := by
    ext q fg
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => (ConeSubset.prepend_comp _ _ _).symm)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The whole supported diagram enters the original cone by its unchanged actual coefficient inclusions. -/
def coneRootBoundaryDiagramInclusion (n : ℕ) : coneRootBoundaryDiagram.{u} n ⟶ coneDiagram n where
  app i := coneRootBoundaryInclusion i.unop.as
  naturality i j := by
    ext q p
    apply Hom.ext
    ext r a
    rfl

/-- The actual whole diagram action is precisely the original restricted root-boundary path map. -/
theorem coneRootBoundaryDiagram_action (n : ℕ) (i j : Vertex.{u} n) :
    enrichedDiagramAction (coneRootBoundaryDiagram n) (op (SimplicialThickening.mk j))
      (op (SimplicialThickening.mk i)) = coneRootBoundaryAction i j := maxUncurry_maxCurry _

end SSet.Marked.CoherentWeight
