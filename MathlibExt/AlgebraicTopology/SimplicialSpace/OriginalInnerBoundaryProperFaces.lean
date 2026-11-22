/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Boundary colimits over all proper simplex injections, including degree zero.
import MathlibExt.AlgebraicTopology.SimplicialSet.ProperFaceBoundary

/-!
# Proper-face colimits for simplex boundaries

The boundary of a standard simplex is the colimit of its full proper-injection diagram,
including dimension zero. Compatible maps from all proper faces descend uniquely to the
boundary, and the canonical inclusions retain their ordinal-map and naturality equations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.OriginalInnerRealization

/-- Each original proper injection factors through the actual inner boundary, with no chosen face
omitted. -/
def properFaceBoundaryInclusion {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    (SSet.stdSimplex.{u}.obj a.obj.right.unop) ⟶ (SSet.boundary.{u} n : SSet.{u}) :=
  SSet.ProperFaceBoundary.properFaceBoundaryInclusion a

/-- The inclusion in the original simplex is exactly the prescribed ordinal map. -/
@[reassoc]
theorem properFaceBoundaryInclusion_ι {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    properFaceBoundaryInclusion.{u} a ≫ (SSet.boundary.{u} n).ι =
      SSet.stdSimplex.map a.obj.hom.unop :=
  SSet.ProperFaceBoundary.properFaceBoundaryInclusion_ι a

/-- Every proper-face morphism retains the original boundary inclusion equation. -/
theorem properFaceBoundaryInclusion_naturality {n : ℕ}
    {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b) :
    SSet.stdSimplex.map g.hom.right.unop ≫ properFaceBoundaryInclusion.{u} a =
      properFaceBoundaryInclusion.{u} b :=
  SSet.ProperFaceBoundary.properFaceBoundaryInclusion_naturality g

/-- The entire opposite matching index is the actual inner proper-simplex face diagram. -/
def properFaceSimplexDiagram (n : ℕ) : (SimplicialObject.matchingIndex n)ᵒᵖ ⥤ SSet.{u} :=
  SSet.ProperFaceBoundary.properFaceSimplexDiagram n

/-- The canonical cocone includes every actual proper injection into the same boundary. -/
def properFaceBoundaryCocone (n : ℕ) : Cocone (properFaceSimplexDiagram.{u} n) :=
  SSet.ProperFaceBoundary.properFaceBoundaryCocone n

/-- Every full proper-face section family descends uniquely to the actual inner boundary. -/
theorem properFaceBoundary_sections (n : ℕ) (Q : SSet.{u})
    (s : ∀ a : SimplicialObject.matchingIndex n, SSet.stdSimplex.obj a.obj.right.unop ⟶ Q)
    (hs : ∀ {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b),
      SSet.stdSimplex.map g.hom.right.unop ≫ s a = s b) :
    ∃! f : (SSet.boundary.{u} n : SSet.{u}) ⟶ Q,
      ∀ a, properFaceBoundaryInclusion a ≫ f = s a :=
  SSet.ProperFaceBoundary.properFaceBoundary_sections n Q s hs

/-- The whole proper-injection diagram is a genuine colimit presentation of the inner boundary. -/
def properFaceBoundaryIsColimit (n : ℕ) : IsColimit (properFaceBoundaryCocone.{u} n) :=
  SSet.ProperFaceBoundary.properFaceBoundaryIsColimit n

end SimplicialSpace.OriginalInnerRealization
