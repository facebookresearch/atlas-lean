/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationCylinder
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkedTensorEnrichment

/-!
# The actual original preceding-stage prism map

The minimal interval and whole preceding cone map to the bounded stage
by inserting the new vertex precisely at the top. The strict least
vertex bound is derived from the original supplied subset, so empty
stage values introduce no additional hypothesis. Whole path union
commutes with this operation in every original scalar degree.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Inserting the selected new vertex commutes with every whole original path union, including both original
  interval endpoints. -/
theorem coneFromFiltration_prepend {n : ℕ} {i j k : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeBefore j k) (t : Vertex.{u} 1) :
    (coneFromFiltration
      (coneBefore_least_lt ((coneBeforePrependFunctor i j k).obj (p, a)))
      ((coneBeforePrependFunctor i j k).obj (p, a), t)).val =
        (coneFromFiltration (coneBefore_least_lt a) (a, t)).val.prepend p := by
  rcases t with ⟨t⟩
  fin_cases t
  · rfl
  · apply ConeSubset.ext
    change insert k (p.I.toFinite.toFinset ∪ a.val.vertices) =
      p.I.toFinite.toFinset ∪ insert k a.val.vertices
    ext l
    simp only [Finset.mem_insert, Finset.mem_union]
    tauto

/-- The original minimal interval and preceding subset form the actual marked stage prism, with its full
  selected marking preserved. -/
def coneBeforeStagePrism {n : ℕ} (i k : Vertex.{u} n) :
    prod (min (Δ[1] : SSet.{u})) (coneBeforeWeight i k) ⟶ coneAtMostWeight i k where
  hom :=
    { app q := ↾fun a => (coneFiltrationFromPrism (coneBefore_least_lt (a.2.obj 0))).app q (a.2, a.1)
      naturality q r f := by
        ext a
        refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _) }
  preserve {e} he :=
    (coneFiltrationCylinderIso (coneBefore_least_lt (e.2.obj 0))).inv.preserve (Or.inl ⟨he.2, he.1⟩)

/-- The entire preceding-stage prism maps to the bounded stage as a genuine enriched natural marked map. -/
def coneBeforeStagePrismMap {n : ℕ} (k : Vertex.{u} n) :
    (enrichedDiagramMarkedTensor (Index.{u} n)ᵒᵖ (min (Δ[1] : SSet.{u}))).obj
      (coneBeforeDiagram k) ⟶ coneAtMostDiagram k where
  app i := coneBeforeStagePrism i.unop.as k
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r z
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_)
      (fun _ _ _ => Subsingleton.elim _ _)
    exact coneFromFiltration_prepend _ _ _

/-- The bottom endpoint retains exactly the whole original preceding-stage inclusion. -/
theorem coneBeforeStagePrism_bottom {n : ℕ} (i k : Vertex.{u} n) :
    markedCylinderBottom (coneBeforeWeight i k) ≫
      (prodSwapIso (coneBeforeWeight i k) (min (Δ[1] : SSet.{u}))).hom ≫
        coneBeforeStagePrism i k = coneBeforeInclusion i k := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply Subtype.ext
  rfl

end SSet.Marked.CoherentWeight
