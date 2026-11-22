/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryAfter

/-!
# The unchanged full positive coefficients of the root boundary

Beyond the original root, both the positive cone and root-boundary
coefficient are the whole original marked cone. Their existing
support isomorphisms identify exactly the same positive inclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Above the original root, the complete positive coefficient is isomorphic to the unchanged complete root-boundary
coefficient. -/
def coneRootBoundaryAfterAboveIso {n : ℕ} {i : Vertex.{u} n}
    (hi : (⊥ : Vertex.{u} n) < i) :
    coneAfterWeight i (⊥ : Vertex.{u} n) ≅ coneRootBoundaryMarked i :=
  coneAfterAboveIso hi ≪≫ (coneRootBoundaryAboveIso hi).symm

/-- The original positive-to-boundary coefficient inclusion is exactly the hom of the two genuine original support
isomorphisms. -/
theorem coneRootBoundaryAfterAboveIso_hom {n : ℕ} {i : Vertex.{u} n}
    (hi : (⊥ : Vertex.{u} n) < i) :
    (coneRootBoundaryAfterAboveIso hi).hom = coneRootBoundaryAfterInclusion i := by
  let e := coneRootBoundaryAboveIso hi
  have : IsIso (coneRootBoundaryInclusion i) :=
    (coneRootBoundaryAboveIso_hom hi) ▸ e.isIso_hom
  apply (cancel_mono (coneRootBoundaryInclusion i)).mp
  have he : e.inv ≫ coneRootBoundaryInclusion i = 𝟙 _ :=
    (congrArg (fun a => e.inv ≫ a) (coneRootBoundaryAboveIso_hom hi).symm).trans e.inv_hom_id
  change ((coneAfterAboveIso hi).hom ≫ e.inv) ≫ coneRootBoundaryInclusion i = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (coneAfterAboveIso hi).hom ≫ a) he).trans
      ((Category.comp_id _).trans
        ((coneAfterAboveIso_hom hi).trans (coneRootBoundaryAfterInclusion_inclusion i).symm)))

end SSet.Marked.CoherentWeight
