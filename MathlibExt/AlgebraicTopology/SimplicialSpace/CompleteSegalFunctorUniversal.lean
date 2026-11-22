/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorCoreMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorNaturality
import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionClosedCurrying
import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionDerivedMaps

/-!
# Universal mapping interpretation of the one-fold closed comparison

For every scalar source, the same weak comparison of native Kan cores gives
a weak map of actual scalar mapping spaces. Its Ho universal comparison
identifies the original one-fold Q/R end. The original groupoidal-source
universal theorem uses that same comparison and its exact original triangle.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialSpace.FirstProjection

private abbrev H : SSet.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization :=
  SSet.realizationWeakEquivalences.Q
private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

private abbrev F := SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1

/-- The literal scalar mapping-space map induced by the original closed comparison's core. -/
def scalarCoreComparison (K : SSet.{u}) (W V : SimplicialSpace.{u}) :
    (ihom K).obj (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) ⟶
      (ihom K).obj (functorCore W V) :=
  (ihom K).map (SSet.coreFunctor.map (comparison W V))

/-- Every scalar source has a weak native mapping-space comparison, with no Kan hypothesis on that source. -/
theorem scalarCoreComparison_weak (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.realizationWeakEquivalences (scalarCoreComparison K W V) := by
  let _ : SSet.Quasicategory (right.obj ((ihom W).obj V)) := comparison_source_quasicategory W V hV
  let _ : SSet.Quasicategory ((ihom (right.obj W)).obj (right.obj V)) :=
    comparison_target_quasicategory W V hV
  let _ : SSet.KanComplex (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) :=
    SSet.kanComplex_core_of_quasicategory _
  let _ : SSet.KanComplex (functorCore W V) := SSet.kanComplex_core_of_quasicategory _
  let _ : IsFibrant (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) := inferInstance
  let _ : IsFibrant (functorCore W V) := inferInstance
  let _ : WeakEquivalence (SSet.coreFunctor.map (comparison W V)) :=
    (weakEquivalence_iff _).mpr (comparison_coreWeak W V hW hV)
  let _ : (ihom.adjunction K).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := ihom.adjunction K) (SSet.coreFunctor.map (comparison W V)))

/-- The comparison retains source contravariance for every literal scalar map. -/
theorem scalarCoreComparison_source {K L : SSet.{u}} (k : K ⟶ L) (W V : SimplicialSpace.{u}) :
    (pre k).app (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) ≫ scalarCoreComparison K W V =
      scalarCoreComparison L W V ≫ (pre k).app (functorCore W V) :=
  (pre k).naturality (SSet.coreFunctor.map (comparison W V))

/-- Every native core map classifies the same actual original Q/R derived end in Ho. -/
def universalHomEquiv (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    (H.{u}.obj K ⟶ H.{u}.obj (functorCore W V)) ≃
      (H.{u}.obj K ⟶ H.{u}.obj (((localDerivedEnd F.{u}).obj (op (originalImage W))).obj
        (originalImage V))) :=
  Iso.homCongr (Iso.refl _) (functorCoreMappingIso W V hW hV)

/-- The universal map is postcomposition by the same original derived-end comparison. -/
theorem universalHomEquiv_apply (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (f : H.{u}.obj K ⟶ H.{u}.obj (functorCore W V)) :
    universalHomEquiv K W V hW hV f = f ≫ (functorCoreMappingIso W V hW hV).hom := by
  simp only [universalHomEquiv, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]

/-- Scalar source maps retain their entire Ho universal action. -/
theorem universalHomEquiv_source {K L : SSet.{u}} (k : K ⟶ L) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (f : H.{u}.obj L ⟶ H.{u}.obj (functorCore W V)) :
    universalHomEquiv K W V hW hV (H.{u}.map k ≫ f) =
      H.{u}.map k ≫ universalHomEquiv L W V hW hV f := by
  simp only [universalHomEquiv_apply, Category.assoc]

/-- The universal comparison commutes with the original weak CSS-to-Joyal core map. -/
theorem universalHomEquiv_triangle (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (f : H.{u}.obj K ⟶ H.{u}.obj (SSet.coreFunctor.obj (right.obj ((ihom W).obj V)))) :
    universalHomEquiv K W V hW hV
        (f ≫ H.{u}.map (SSet.coreFunctor.map (comparison W V))) =
      f ≫ (cssPowerCoreMappingIso W V hV).hom := by
  rw [universalHomEquiv_apply, Category.assoc, functorCoreMappingIso_triangle]

/-- The original one-fold native core maps to the same actual scalar functor core. -/
def originalCoreToFunctorIso (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    H.{u}.obj ((SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeCoreFunctor (originalImage W)).obj
      (originalImage V)) ≅ H.{u}.obj (functorCore W V) :=
  H.{u}.mapIso (originalNativeCoreIso W V) ≪≫
    (comparisonCoreNatIso.app (op ⟨W, hW⟩)).app ⟨V, hV⟩

/-- The original groupoidal-source maps classify the actual arbitrary-source native functor core. -/
def originalUniversalHomEquiv (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    ((SimplicialPresheaf.CoreDerivedAdjunction.localHo F.{u}).obj
        (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo F.{u}).obj
        (SimplicialPresheaf.OrderedJFS.OneFunctor.object (originalImage W) (originalImage V))) ≃
    (H.{u}.obj K ⟶ H.{u}.obj (functorCore W V)) :=
  (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeUniversalHomEquiv
    (originalImage W) K (originalImage V) (originalImage_local V hV)).trans
      (Iso.homCongr (Iso.refl _) (originalCoreToFunctorIso W V hW hV))

/-- The universal application has exactly the same checked original-zero/Q/R derived-end triangle. -/
theorem originalUniversalHomEquiv_derived (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (f : (SimplicialPresheaf.CoreDerivedAdjunction.localHo F.{u}).obj
        (SimplicialPresheaf.OrderedJFS.OneFunctor.Core.groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo F.{u}).obj
        (SimplicialPresheaf.OrderedJFS.OneFunctor.object (originalImage W) (originalImage V))) :
    universalHomEquiv K W V hW hV (originalUniversalHomEquiv K W V hW hV f) =
      SimplicialPresheaf.OrderedJFS.OneFunctor.Core.homEquiv (originalImage W) K
        (originalImage V) (originalImage_local V hV) f := by
  rw [universalHomEquiv_apply]
  rw [originalUniversalHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  change ((SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeUniversalHomEquiv
      (originalImage W) K (originalImage V) (originalImage_local V hV) f) ≫
    ((H.{u}.mapIso (originalNativeCoreIso W V)).hom ≫
      H.{u}.map (SSet.coreFunctor.map (comparison W V)))) ≫
    (functorCoreMappingIso W V hW hV).hom = _
  rw [Category.assoc, Category.assoc, functorCoreMappingIso_triangle]
  erw [cssPowerCoreMappingIso_original]
  exact SimplicialPresheaf.OrderedJFS.OneFunctor.Core.nativeUniversalHomEquiv_derived
    (originalImage W) K (originalImage V) (originalImage_local V hV) f

end SimplicialSpace.FirstProjection
