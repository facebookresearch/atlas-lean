/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningHomNaturality
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The actual native one-fold marked straightening/unstraightening adjunction

The object construction is the actual marked colimit of original
coherent simplex and sharp-edge charts. Its proven whole universal
maps and target naturality instantiate the canonical adjoint
construction. The original unit, counit and both complete triangles
are therefore proved, not supplied as outcomes. This is the native
categorical adjunction; model and derived equivalence statements are
separate claims to prove.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The native straightening functor uses the actual marked chart colimits and constructed whole universal maps. -/
def nativeStraightening (B : SSet.{u}) : Over (max B) ⥤ EnrichedDiagram (realization B)ᵒᵖ :=
  Adjunction.leftAdjointOfEquiv (nativeStraighteningHomEquiv B)
    (fun X F G φ f => nativeStraighteningHomEquiv_natural_right B X (F := F) (G := G) f φ)

/-- The actual native marked straightening/unstraightening adjunction, with all Hom maps and triangles constructed. -/
def nativeStraighteningAdjunction (B : SSet.{u}) : nativeStraightening B ⊣ nativeUnstraightening B :=
  Adjunction.adjunctionOfEquivLeft (nativeStraighteningHomEquiv B)
    (fun X F G φ f => nativeStraighteningHomEquiv_natural_right B X (F := F) (G := G) f φ)

/-- Its entire original straightening object is the actual marked chart colimit, with no substitute presentation. -/
theorem nativeStraightening_obj (B : SSet.{u}) (X : Over (max B)) :
    (nativeStraightening B).obj X = nativeStraighteningObject B X := rfl

/-- The actual native adjunction unit is precisely the original marked basis-density universal map. -/
theorem nativeStraighteningAdjunction_unit (B : SSet.{u}) (X : Over (max B)) :
    (nativeStraighteningAdjunction B).unit.app X =
      nativeStraighteningForward B X (nativeStraighteningObject B X) (𝟙 _) := rfl

/-- The actual native counit is precisely the whole marked chart-colimit descent of the original identity map. -/
theorem nativeStraighteningAdjunction_counit (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeStraighteningAdjunction B).counit.app F =
      nativeStraighteningBackward B ((nativeUnstraightening B).obj F) F (𝟙 _) := rfl

/-- Every entire original marked source map straightens through its original target unit and native
  universal inverse. -/
theorem nativeStraightening_map (B : SSet.{u}) {X Y : Over (max B)} (f : X ⟶ Y) :
    (nativeStraightening B).map f =
      nativeStraighteningBackward B X (nativeStraighteningObject B Y)
        (f ≫ nativeStraighteningForward B Y (nativeStraighteningObject B Y) (𝟙 _)) := rfl

/-- The whole original straightening triangle is the identity on the actual marked chart colimit. -/
theorem nativeStraightening_left_triangle (B : SSet.{u}) (X : Over (max B)) :
    (nativeStraightening B).map ((nativeStraighteningAdjunction B).unit.app X) ≫
      (nativeStraighteningAdjunction B).counit.app ((nativeStraightening B).obj X) = 𝟙 _ :=
  (nativeStraighteningAdjunction B).left_triangle_components X

/-- The whole original unstraightening triangle retains the identity on its actual marked total space and base map. -/
theorem nativeStraightening_right_triangle (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeStraighteningAdjunction B).unit.app ((nativeUnstraightening B).obj F) ≫
      (nativeUnstraightening B).map ((nativeStraighteningAdjunction B).counit.app F) = 𝟙 _ :=
  (nativeStraighteningAdjunction B).right_triangle_components F

/-- The actual native straightening functor preserves original coefficient-sized colimits through its
  constructed adjunction. -/
theorem nativeStraightening_preservesColimits (B : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (nativeStraightening B) :=
  (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits

end SSet.Marked
