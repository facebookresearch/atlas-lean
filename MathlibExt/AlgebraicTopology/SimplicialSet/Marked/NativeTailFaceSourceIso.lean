/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeTailBaseIndex
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootRelativeCofibration
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailLeftKanComparison

/-!
# The actual original native zeroth-face source

The original coherent base operator identifies the composed tail
restriction with the actual restricted base simplex. Canonical
uniqueness of their existing native adjunctions and the proved whole
tail coefficient comparison give the genuine zeroth-face chart source
isomorphism. Its construction retains the original unit maps and
the actual left-extension objects over the original base.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual tail and base left-extension adjunctions compose to the same original zeroth-face restriction. -/
def nativeTailCompositeAdjunction (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    EnrichedLeftKan.leftExtension (coneTailIndex n) ⋙
        EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ)) ⊣
      enrichedDiagramRestrict
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))) :=
  ((EnrichedLeftKan.adjunction (coneTailIndex n)).comp
    (EnrichedLeftKan.adjunction (EnrichedFunctor.opposite (simplexInto B σ)))).ofNatIsoRight
      (eqToIso (nativeTail_restriction_comp B n σ))

/-- The actual composed native left extension has the canonical whole comparison with the original
  zeroth-face left extension. -/
def nativeTailCompositeNatIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    EnrichedLeftKan.leftExtension (coneTailIndex n) ⋙
        EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ)) ≅
      EnrichedLeftKan.leftExtension
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))) :=
  Adjunction.leftAdjointUniq (nativeTailCompositeAdjunction B n σ)
    (EnrichedLeftKan.adjunction
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))))

/-- The whole native composite comparison is the actual transpose of the original restricted-simplex unit. -/
theorem nativeTailComposite_hom_unit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (W : EnrichedDiagram (Index.{u} n)ᵒᵖ) :
    (nativeTailCompositeAdjunction B n σ).homEquiv _ _ ((nativeTailCompositeNatIso B n σ).hom.app W) =
      (EnrichedLeftKan.adjunction
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)))).unit.app W :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ W

/-- The actual whole zeroth-face chart source is the original positive-root chart over the same original
  base simplex. -/
def nativeTailFaceSourceIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeSimplexChart B n (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ) ≅
      nativePositiveRootChart B (n + 1) σ :=
  (nativeTailCompositeNatIso B n σ).symm.app (coneDiagram n) ≪≫
    (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).mapIso (coneTailLeftKanIso n)

/-- The original source comparison keeps its exact canonical composite-unit inverse and whole actual tail mate. -/
theorem nativeTailFaceSourceIso_hom (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeTailFaceSourceIso B n σ).hom =
      (nativeTailCompositeNatIso B n σ).inv.app (coneDiagram n) ≫
        (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneTailLeftKanMap n) := rfl

end SSet.Marked
