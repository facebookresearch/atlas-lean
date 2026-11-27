/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFunctor

/-!
# The actual marked enriched left-extension and restriction adjunction

The left functor is the proved whole-Hom coequalizer construction. The
right functor is original enriched restriction. Both Hom naturalities,
the actual unit and counit and both whole triangles follow from the
constructed universal correspondence. No adjunction or equivalence
certificate is assumed.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D)

/-- Actual marked enriched left extension is left adjoint to the original whole restriction functor. -/
def adjunction : leftExtension j ⊣ enrichedDiagramRestrict j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := universalHomEquiv j
      homEquiv_naturality_left_symm := by
        intro W V X φ g
        apply (universalHomEquiv j W X).injective
        let g' : V ⟶ j.comp SSet.{u} X := g
        let f : object j V ⟶ X := (universalHomEquiv j V X).symm g'
        let rf : j.comp SSet.{u} (object j V) ⟶ j.comp SSet.{u} X := (enrichedDiagramRestrict j).map f
        have hg : unit j V ≫ rf = g' :=
          (universalHomEquiv_unit j V X f).symm.trans
            ((universalHomEquiv j V X).apply_symm_apply g')
        calc
          universalHomEquiv j W X ((universalHomEquiv j W X).symm (φ ≫ g')) = φ ≫ g' :=
            (universalHomEquiv j W X).apply_symm_apply _
          _ = φ ≫ (unit j V ≫ rf) :=
            congrArg (fun t => φ ≫ t) hg.symm
          _ = (φ ≫ unit j V) ≫ rf := (Category.assoc _ _ _).symm
          _ = universalHomEquiv j W (object j V) (map j φ) ≫ rf :=
            congrArg (fun t => t ≫ rf) (map_homEquiv j φ).symm
          _ = universalHomEquiv j W X (map j φ ≫ f) :=
            (universalHomEquiv_natural_right j W (map j φ) f).symm
      homEquiv_naturality_right := by
        intro W X Y f g
        exact universalHomEquiv_natural_right j W f g }

/-- The actual adjunction unit is exactly the constructed original identity-coequalizer universal map. -/
theorem adjunction_unit (W : EnrichedDiagram C) : (adjunction j).unit.app W = unit j W := rfl

/-- The actual adjunction counit is the native inverse universal map on the original restricted identity. -/
theorem adjunction_counit (X : EnrichedDiagram D) :
    (adjunction j).counit.app X =
      (universalHomEquiv j ((enrichedDiagramRestrict j).obj X) X).symm (𝟙 ((enrichedDiagramRestrict j).obj X)) :=
  rfl

/-- The whole original left-extension triangle is the identity on its actual selected coequalizer. -/
theorem left_triangle (W : EnrichedDiagram C) :
    (leftExtension j).map ((adjunction j).unit.app W) ≫
      (adjunction j).counit.app ((leftExtension j).obj W) = 𝟙 _ :=
  (adjunction j).left_triangle_components W

/-- The entire original restriction triangle is the identity on its actual marked enriched diagram. -/
theorem right_triangle (X : EnrichedDiagram D) :
    (adjunction j).unit.app ((enrichedDiagramRestrict j).obj X) ≫
      (enrichedDiagramRestrict j).map ((adjunction j).counit.app X) = 𝟙 _ :=
  (adjunction j).right_triangle_components X

end SSet.Marked.EnrichedLeftKan
