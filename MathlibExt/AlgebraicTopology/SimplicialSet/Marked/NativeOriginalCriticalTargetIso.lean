/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalMarkingSpanComparisons

/-!
# The same ORIGINAL native critically marked simplex Target Iso

Native straightening preserves the genuine original target marking
pushout. Its full original span is the critically marked native
simplex marking span through actual whole basis identities and unit
mates. Actual colimit uniqueness proves the entire target isomorphism
and BOTH identities, retaining every supplied original base map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME original critically marked full simplex has its actual whole native supported target isomorphism over
the supplied original simplex. -/
def nativeOriginalCriticalTargetCanonicalIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeStraightening B).obj (Over.mk (nativeCriticalProjection B n σ)) ≅
      nativeCriticalSupportedSimplexChart B n σ :=
  IsColimit.coconePointsIsoOfNatIso
    (nativeCriticalTargetImageMarkingIsColimit B n (nativeCriticalProjection B n σ))
    (nativeCriticalWholeConeEdgeMarkingIsColimit B n σ) (nativeOriginalCriticalTargetMarkingSpanIso B n σ)

/-- Every complete original target marking leg retains its SAME full original span unit mate. -/
theorem nativeOriginalCriticalTargetCanonicalIso_leg (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : WalkingSpan) :
    (nativeCriticalTargetImageMarkingCocone B n (nativeCriticalProjection B n σ)).ι.app j ≫
      (nativeOriginalCriticalTargetCanonicalIso B n σ).hom =
    (nativeOriginalCriticalTargetMarkingSpanIso B n σ).hom.app j ≫
      (nativeCriticalWholeConeEdgeMarkingCocone B n σ).ι.app j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (nativeCriticalTargetImageMarkingIsColimit B n (nativeCriticalProjection B n σ))
    (nativeCriticalWholeConeEdgeMarkingIsColimit B n σ) (nativeOriginalCriticalTargetMarkingSpanIso B n σ) j

/-- Every arbitrary original whole marked target-to-base map retains its SAME actual full native critical Target Iso. -/
def nativeOriginalCriticalTargetIso (B : SSet.{u}) (n : ℕ) (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeStraightening B).obj (Over.mk r) ≅
      nativeCriticalSupportedSimplexChart B n (SSet.yonedaEquiv r.hom) :=
  eqToIso (congrArg (fun q : cartesianCriticalTarget n ⟶ max B =>
    (nativeStraightening B).obj (Over.mk q)) (nativeCriticalProjection_original B n r).symm) ≪≫
      nativeOriginalCriticalTargetCanonicalIso B n (SSet.yonedaEquiv r.hom)

/-- The SAME whole original physical critically marked target is recovered by both forward and inverse maps. -/
theorem nativeOriginalCriticalTargetIso_hom_inv_id (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeOriginalCriticalTargetIso B n r).hom ≫ (nativeOriginalCriticalTargetIso B n r).inv = 𝟙 _ :=
  (nativeOriginalCriticalTargetIso B n r).hom_inv_id

/-- The entire SAME supported critically marked simplex target is recovered by both inverse and forward maps. -/
theorem nativeOriginalCriticalTargetIso_inv_hom_id (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeOriginalCriticalTargetIso B n r).inv ≫ (nativeOriginalCriticalTargetIso B n r).hom = 𝟙 _ :=
  (nativeOriginalCriticalTargetIso B n r).inv_hom_id

end SSet.Marked
