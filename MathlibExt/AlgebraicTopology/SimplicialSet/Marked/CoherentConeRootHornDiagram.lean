/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornSupport
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# The SAME original supported marked enriched root-horn diagram

The original whole cone action restricts to the entire original horn at
root and whole original cone coefficients above root. Its full marked
action retains every original path and scalar word. The original identity
and composition laws give the genuine whole enriched diagram and its
literal original inclusion in the complete original cone.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The complete original path action restricts to the SAME actual horn support and its unchanged inherited maximum
marking. -/
def coneRootHornAction {n : ℕ} (k : Fin (n + 2)) (i j : Vertex.{u} (n + 1)) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneRootHornMarked k j) ⟶ coneRootHornMarked k i where
  hom :=
    { app q := ↾fun x => ⟨(coneAction i j).hom.app q (x.1, x.2.val),
        coneRootHornSupport_action_mem k i j q x.1 x.2.val x.2.property⟩
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact congr($((coneAction i j).hom.naturality f) (x.1, x.2.val)) }
  preserve {e} he := (coneAction i j).preserve (show
    (e.1, e.2.val) ∈ (prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j)).marking from
      ⟨he.1, he.2⟩)

/-- The SAME original supported coefficients and all original path actions form the entire original marked enriched
horn diagram. -/
def coneRootHornDiagram {n : ℕ} (k : Fin (n + 2)) : EnrichedDiagram (Index.{u} (n + 1))ᵒᵖ where
  obj i := coneRootHornMarked k i.unop.as
  map i j := maxCurry (coneRootHornAction k j.unop.as i.unop.as)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ConeSubset.prepend_id _) (fun _ _ _ => Subsingleton.elim _ _)
  map_comp i j m := by
    ext q fg
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => (ConeSubset.prepend_comp _ _ _).symm)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The SAME entire original supported horn diagram enters the whole original cone by its unchanged full coefficient
inclusions. -/
def coneRootHornDiagramInclusion {n : ℕ} (k : Fin (n + 2)) : coneRootHornDiagram.{u} k ⟶ coneDiagram (n + 1) where
  app i := coneRootHornInclusion k i.unop.as
  naturality i j := by
    ext q p
    apply Hom.ext
    ext r a
    rfl

/-- The full original enriched horn action retains precisely its SAME original path action restricted to the
unchanged root and positive supports. -/
theorem coneRootHornDiagram_action {n : ℕ} (k : Fin (n + 2)) (i j : Vertex.{u} (n + 1)) :
    enrichedDiagramAction (coneRootHornDiagram k) (op (SimplicialThickening.mk j))
      (op (SimplicialThickening.mk i)) = coneRootHornAction k i j := maxUncurry_maxCurry _

end SSet.Marked.CoherentWeight
