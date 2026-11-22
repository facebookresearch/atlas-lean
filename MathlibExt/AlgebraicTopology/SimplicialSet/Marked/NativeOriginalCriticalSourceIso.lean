/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalMarkingSpanComparisons

/-!
# The same ORIGINAL native critically marked horn Source Iso

The actual original source marking pushout is preserved by native
straightening. Its entire span agrees with the full critically marked
supported horn marking pushout through the original basis records and
unit mates. Genuine colimit uniqueness gives the whole marked source
isomorphism and BOTH identities, for every original whole base map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME original critically marked horn over the supplied whole simplex has its genuine entire native supported
source isomorphism. -/
def nativeOriginalCriticalSourceCanonicalIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeStraightening B).obj (Over.mk (cartesianCriticalCell n ≫ nativeCriticalProjection B n σ)) ≅
      nativeCriticalSupportedHornChart B n σ :=
  IsColimit.coconePointsIsoOfNatIso
    (nativeCriticalSourceImageMarkingIsColimit B n (nativeCriticalProjection B n σ))
    (nativeCriticalWholeHornEdgeMarkingIsColimit B n σ) (nativeOriginalCriticalSourceMarkingSpanIso B n σ)

/-- Every complete original source marking leg retains precisely its SAME entire original span unit mate. -/
theorem nativeOriginalCriticalSourceCanonicalIso_leg (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : WalkingSpan) :
    (nativeCriticalSourceImageMarkingCocone B n (nativeCriticalProjection B n σ)).ι.app j ≫
      (nativeOriginalCriticalSourceCanonicalIso B n σ).hom =
    (nativeOriginalCriticalSourceMarkingSpanIso B n σ).hom.app j ≫
      (nativeCriticalWholeHornEdgeMarkingCocone B n σ).ι.app j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (nativeCriticalSourceImageMarkingIsColimit B n (nativeCriticalProjection B n σ))
    (nativeCriticalWholeHornEdgeMarkingIsColimit B n σ) (nativeOriginalCriticalSourceMarkingSpanIso B n σ) j

/-- Every SAME original whole marked critical source over an arbitrary supplied original base map has its actual
full supported Source Iso. -/
def nativeOriginalCriticalSourceIso (B : SSet.{u}) (n : ℕ) (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeStraightening B).obj (Over.mk (cartesianCriticalCell n ≫ r)) ≅
      nativeCriticalSupportedHornChart B n (SSet.yonedaEquiv r.hom) :=
  eqToIso (congrArg (fun q : cartesianCriticalTarget n ⟶ max B =>
    (nativeStraightening B).obj (Over.mk (cartesianCriticalCell n ≫ q)))
      (nativeCriticalProjection_original B n r).symm) ≪≫
    nativeOriginalCriticalSourceCanonicalIso B n (SSet.yonedaEquiv r.hom)

/-- The SAME entire original physical critical horn source is recovered by its full forward and inverse marked maps. -/
theorem nativeOriginalCriticalSourceIso_hom_inv_id (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeOriginalCriticalSourceIso B n r).hom ≫ (nativeOriginalCriticalSourceIso B n r).inv = 𝟙 _ :=
  (nativeOriginalCriticalSourceIso B n r).hom_inv_id

/-- The entire SAME supported critically marked horn source is recovered by both original inverse and forward maps. -/
theorem nativeOriginalCriticalSourceIso_inv_hom_id (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeOriginalCriticalSourceIso B n r).inv ≫ (nativeOriginalCriticalSourceIso B n r).hom = 𝟙 _ :=
  (nativeOriginalCriticalSourceIso B n r).inv_hom_id

end SSet.Marked
