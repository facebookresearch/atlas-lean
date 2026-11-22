/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryCell

/-!
# The original positive cone enters the same complete root boundary

At the root, the first positive maximum of a whole original subset
word is retained at every later scalar vertex. Thus every original
positive word lies on its actual upper coordinate face. Above the
root the support is the whole original cone. The same original
positive-maximum inclusion therefore factors through the actual
supported enriched diagram with unchanged markings and path action.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Every whole original positive cone word lies in the same actual complete root-boundary support. -/
theorem coneRootBoundaryAfter_mem {n : ℕ} (i : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (a : (nerve (ConeAfter i (⊥ : Vertex.{u} n))).obj q) :
    (coneAfterInclusion i (⊥ : Vertex.{u} n)).hom.app q a ∈ (coneRootBoundarySupport i).obj q := by
  by_cases hi : i = ⊥
  · subst i
    rw [coneRootBoundarySupport_root n]
    apply (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} n) _).mpr
    refine ⟨⟨(a.obj 0).val.maximum, (a.obj 0).property⟩, true, fun t => ?_⟩
    simp only [iff_true]
    change (a.obj 0).val.maximum ∈ (a.obj t).val.vertices
    have ht : (a.obj 0).val.vertices ⊆ (a.obj t).val.vertices :=
      leOfHom (a.map (homOfLE (Fin.zero_le t)))
    exact ht (a.obj 0).val.maximum_mem
  · rw [coneRootBoundarySupport, ite_eq_right hi]
    exact Set.mem_univ _

/-- The whole original positive coefficient enters the same marked root-boundary support through its unchanged
inclusion. -/
def coneRootBoundaryAfterInclusion {n : ℕ} (i : Vertex.{u} n) :
    coneAfterWeight i (⊥ : Vertex.{u} n) ⟶ coneRootBoundaryMarked i where
  hom :=
    { app q := ↾fun a => ⟨(coneAfterInclusion i (⊥ : Vertex.{u} n)).hom.app q a,
        coneRootBoundaryAfter_mem i a⟩
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro a
        apply Subtype.ext
        exact congr($((coneAfterInclusion i (⊥ : Vertex.{u} n)).hom.naturality f) a) }
  preserve {e} he := (coneAfterInclusion i (⊥ : Vertex.{u} n)).preserve he

/-- The actual positive coefficient retains precisely the unchanged original positive cone inclusion. -/
theorem coneRootBoundaryAfterInclusion_inclusion {n : ℕ} (i : Vertex.{u} n) :
    coneRootBoundaryAfterInclusion i ≫ coneRootBoundaryInclusion i =
      coneAfterInclusion i (⊥ : Vertex.{u} n) := by
  apply Hom.ext
  rfl

/-- All original positive coefficients and whole path actions factor through the same complete marked root-boundary
diagram. -/
def coneRootBoundaryAfterMap (n : ℕ) :
    coneAfterDiagram (⊥ : Vertex.{u} n) ⟶ coneRootBoundaryDiagram n where
  app i := coneRootBoundaryAfterInclusion i.unop.as
  naturality i j := by
    ext q p
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The full positive cone map has exactly its original whole attaching inclusion after entering the same supported
diagram. -/
theorem coneRootBoundaryAfterMap_inclusion (n : ℕ) :
    coneRootBoundaryAfterMap.{u} n ≫ coneRootBoundaryDiagramInclusion n =
      coneAfterDiagramInclusion (⊥ : Vertex.{u} n) := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneRootBoundaryAfterInclusion_inclusion i.unop.as

end SSet.Marked.CoherentWeight
