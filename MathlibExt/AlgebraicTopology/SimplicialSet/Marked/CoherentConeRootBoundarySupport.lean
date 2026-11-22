/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationEndpoints
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Original coordinate-boundary support at the cone root

At the original root retain its complete marked coordinate boundary.
Above the root retain the whole original cone coefficient. Original
path prepending preserves these supports: a positive source vertex
is retained throughout the whole word, and a root self-path is its
original identity. No identification with a native boundary chart is
assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original root retains its complete coordinate boundary; every positive coefficient retains its whole cone. -/
def coneRootBoundarySupport {n : ℕ} (i : Vertex.{u} n) : (nerve (ConeSubset i)).Subcomplex :=
  if i = ⊥ then coneCoordinateBoundary i else ⊤

/-- The original root support is exactly its whole original coordinate boundary. -/
theorem coneRootBoundarySupport_root (n : ℕ) :
    coneRootBoundarySupport (⊥ : Vertex.{u} n) = coneCoordinateBoundary ⊥ := by
  simp [coneRootBoundarySupport]

/-- Above the root, the original support is the whole original cone coefficient. -/
theorem coneRootBoundarySupport_above {n : ℕ} {i : Vertex.{u} n} (hi : (⊥ : Vertex.{u} n) < i) :
    coneRootBoundarySupport i = ⊤ := by
  simp [coneRootBoundarySupport, ne_of_gt hi]

/-- Every whole original path action preserves the root-boundary and positive-coefficient supports. -/
theorem coneRootBoundarySupport_action_mem {n : ℕ} (i j : Vertex.{u} n)
    (q : SimplexCategoryᵒᵖ) (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (a : (nerve (ConeSubset j)).obj q) (ha : a ∈ (coneRootBoundarySupport j).obj q) :
    (coneAction i j).hom.app q (p, a) ∈ (coneRootBoundarySupport i).obj q := by
  by_cases hi : i = ⊥
  · subst i
    by_cases hj : j = ⊥
    · subst j
      have h : (coneAction (⊥ : Vertex.{u} n) ⊥).hom.app q (p, a) = a := by
        refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
        change (a.obj t).prepend (p.obj t) = a.obj t
        exact (congrArg
          (fun x : SimplicialThickening.Path (⊥ : Vertex.{u} n) ⊥ => (a.obj t).prepend x)
          (coneSelfPath_eq_id (p.obj t))).trans (ConeSubset.prepend_id (a.obj t))
      exact h.symm ▸ ha
    · have hpos : (⊥ : Vertex.{u} n) < j := lt_of_le_of_ne bot_le (Ne.symm hj)
      change (coneAction (⊥ : Vertex.{u} n) j).hom.app q (p, a) ∈ (coneCoordinateBoundary ⊥).obj q
      apply (mem_coneCoordinateBoundary_iff ⊥ _).mpr
      refine ⟨⟨j, hpos⟩, true, fun t => ?_⟩
      simp only [iff_true]
      change j ∈ (p.obj t).I.toFinite.toFinset ∪ (a.obj t).vertices
      exact Finset.mem_union_right _ (a.obj t).mem
  · have hs : coneRootBoundarySupport i = ⊤ := by simp [coneRootBoundarySupport, hi]
    rw [hs]
    exact Set.mem_univ _

/-- The whole original support inherits precisely the original maximum-preserving marks. -/
def coneRootBoundaryMarked {n : ℕ} (i : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (coneRootBoundarySupport i).ι

/-- The original supported coefficient enters the whole original marked cone by its unchanged inclusion. -/
def coneRootBoundaryInclusion {n : ℕ} (i : Vertex.{u} n) : coneRootBoundaryMarked i ⟶ coneWeight i :=
  comapHom (coneWeight i) (coneRootBoundarySupport i).ι

/-- At every positive original coefficient, the original support inclusion is its genuine whole marked isomorphism. -/
def coneRootBoundaryAboveIso {n : ℕ} {i : Vertex.{u} n} (hi : (⊥ : Vertex.{u} n) < i) :
    coneRootBoundaryMarked i ≅ coneWeight i :=
  isoMk (Subcomplex.eqToIso (coneRootBoundarySupport_above hi) ≪≫ Subcomplex.topIso (nerve (ConeSubset i)))
    (fun _ => Iff.rfl)

/-- The positive support isomorphism keeps exactly the original coefficient inclusion. -/
theorem coneRootBoundaryAboveIso_hom {n : ℕ} {i : Vertex.{u} n} (hi : (⊥ : Vertex.{u} n) < i) :
    (coneRootBoundaryAboveIso hi).hom = coneRootBoundaryInclusion i := by
  apply Hom.ext
  rfl

end SSet.Marked.CoherentWeight
