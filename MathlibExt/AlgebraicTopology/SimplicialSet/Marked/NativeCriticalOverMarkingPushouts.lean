/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalMarkingPushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalMappingWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningAdjunction
import Mathlib.CategoryTheory.Limits.Over

/-!
# Actual original critical marking pushouts over the unchanged base

Both original full marking cocones lift along the supplied whole
target-to-base map. The forgetful functor creates their genuine slice
colimits, and the actual native adjunction preserves them. The points
are precisely straightening of the original critical source and target;
no identification with a supported enriched object is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original critical source marking span retains every full composite to the actual base. -/
def nativeCriticalSourceOverMarkingDiagram (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) : WalkingSpan ⥤ Over (max B) :=
  Over.lift (span edgeMarkCell
      (selectedEdgeMinimalMap (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n)))
    ((cartesianCriticalSourceMarkingCocone n).ι ≫
      (Functor.const WalkingSpan).map (cartesianCriticalCell n ≫ r))

/-- The entire original source marking cocone lies over precisely the supplied original projection. -/
def nativeCriticalSourceOverMarkingCocone (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    Cocone (nativeCriticalSourceOverMarkingDiagram B n r) :=
  Over.liftCocone (cartesianCriticalSourceMarkingCocone n) (cartesianCriticalCell n ≫ r)

/-- The source cocone point is the original physical source of the same critical slice cell. -/
theorem nativeCriticalSourceOverMarkingCocone_point (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeCriticalSourceOverMarkingCocone B n r).pt = Over.mk (cartesianCriticalCell n ≫ r) := rfl

/-- The complete original source cocone retains its whole original marked sharp edge leg. -/
theorem nativeCriticalSourceOverMarkingCocone_sharp (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    ((nativeCriticalSourceOverMarkingCocone B n r).ι.app WalkingSpan.left).left =
      cartesianCriticalSourceSharpLeg n := rfl

/-- The complete original source cocone retains the identity on every original minimal horn simplex. -/
theorem nativeCriticalSourceOverMarkingCocone_minimal (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    ((nativeCriticalSourceOverMarkingCocone B n r).ι.app WalkingSpan.right).left =
      cartesianCriticalSourceMinimalLeg n := rfl

/-- The entire ORIGINAL source marking cocone is an actual colimit over the same original base. -/
def nativeCriticalSourceOverMarkingIsColimit (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    IsColimit (nativeCriticalSourceOverMarkingCocone B n r) :=
  Over.isColimitLiftCocone _ _ (cartesianCriticalSourceMarkingIsColimit n)

/-- The same original target marking span retains every whole original map to the supplied base. -/
def nativeCriticalTargetOverMarkingDiagram (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) : WalkingSpan ⥤ Over (max B) :=
  Over.lift (span edgeMarkCell
      (selectedEdgeMinimalMap (Δ[n + 2] : SSet.{u}) (cartesianCriticalImageEdge n)))
    ((cartesianCriticalTargetMarkingCocone n).ι ≫ (Functor.const WalkingSpan).map r)

/-- The complete ORIGINAL critical target is the point of its actual marking cocone over the unchanged base. -/
def nativeCriticalTargetOverMarkingCocone (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    Cocone (nativeCriticalTargetOverMarkingDiagram B n r) :=
  Over.liftCocone (cartesianCriticalTargetMarkingCocone n) r

/-- The target cocone point is the original physical target of the same critical slice cell. -/
theorem nativeCriticalTargetOverMarkingCocone_point (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeCriticalTargetOverMarkingCocone B n r).pt = Over.mk r := rfl

/-- The whole original target cocone retains the sharp leg of the SAME original critical edge image. -/
theorem nativeCriticalTargetOverMarkingCocone_sharp (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    ((nativeCriticalTargetOverMarkingCocone B n r).ι.app WalkingSpan.left).left =
      cartesianCriticalTargetSharpLeg n := rfl

/-- The target's entire original minimal carrier is retained by the actual marking cocone. -/
theorem nativeCriticalTargetOverMarkingCocone_minimal (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    ((nativeCriticalTargetOverMarkingCocone B n r).ι.app WalkingSpan.right).left =
      cartesianCriticalTargetMinimalLeg n := rfl

/-- The complete ORIGINAL target marking cocone is a genuine colimit over its actual whole base map. -/
def nativeCriticalTargetOverMarkingIsColimit (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    IsColimit (nativeCriticalTargetOverMarkingCocone B n r) :=
  Over.isColimitLiftCocone _ _ (cartesianCriticalTargetMarkingIsColimit n)

/-- Actual native straightening of the original critical SOURCE marking span and its full cocone. -/
def nativeCriticalSourceImageMarkingCocone (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    Cocone (nativeCriticalSourceOverMarkingDiagram B n r ⋙ nativeStraightening B) :=
  (nativeStraightening B).mapCocone (nativeCriticalSourceOverMarkingCocone B n r)

/-- The actual native adjunction preserves the entire ORIGINAL source marking pushout. -/
def nativeCriticalSourceImageMarkingIsColimit (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    IsColimit (nativeCriticalSourceImageMarkingCocone B n r) := by
  let _ := nativeStraightening_preservesColimits B
  exact isColimitOfPreserves (nativeStraightening B) (nativeCriticalSourceOverMarkingIsColimit B n r)

/-- Actual native straightening of the original critical TARGET marking span and its full cocone. -/
def nativeCriticalTargetImageMarkingCocone (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    Cocone (nativeCriticalTargetOverMarkingDiagram B n r ⋙ nativeStraightening B) :=
  (nativeStraightening B).mapCocone (nativeCriticalTargetOverMarkingCocone B n r)

/-- The actual native adjunction preserves the complete ORIGINAL target marking pushout. -/
def nativeCriticalTargetImageMarkingIsColimit (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    IsColimit (nativeCriticalTargetImageMarkingCocone B n r) := by
  let _ := nativeStraightening_preservesColimits B
  exact isColimitOfPreserves (nativeStraightening B) (nativeCriticalTargetOverMarkingIsColimit B n r)

end SSet.Marked
