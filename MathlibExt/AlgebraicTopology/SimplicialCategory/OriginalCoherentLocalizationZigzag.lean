/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentLocalizationFunctors

/-!
# The actual coherent replacement unit and counit in ordinary localization

Every original replacement unit becomes invertible after categorical
localization. At an arbitrary enrichment, the original counit evaluated
on its genuine locally Kan native replacement is DK weak. Composing its
localized image with the formal inverse of the actual native inclusion
gives the reverse comparison.

The left triangle is the projection of the original inclusion/counit
factorization, followed by the actual formal inverse of that inclusion.
Neither raw counits at nonfibrant objects nor raw nerves at arbitrary
enrichments are claimed to preserve weakness.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalCoherentLocalization

open SimplicialEnrichment

/-- The same original weak native inclusion becomes a natural isomorphism after DK localization. -/
def projectedNativeInclusionIso : enrichmentProjection.{u} ≅
    OriginalBergnerFibrantReplacement.functor.{u} ⋙ enrichmentProjection.{u} :=
  NatIso.ofComponents (fun C => Localization.Construction.wIso
    (OriginalBergnerFibrantReplacement.inclusion.app C)
    (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2) (by
      intro C D F
      exact (Functor.whiskerRight OriginalBergnerFibrantReplacement.inclusion
        enrichmentProjection).naturality F)

/-- The projected inclusion component is the image of the same original native inclusion. -/
theorem projectedNativeInclusionIso_hom_app (C : Carrier.{u}) :
    projectedNativeInclusionIso.hom.app C =
      enrichmentProjection.map (OriginalBergnerFibrantReplacement.inclusion.app C) := rfl

/-- Its inverse is the actual formal inverse of the same weak native inclusion. -/
theorem projectedNativeInclusionIso_inv_app (C : Carrier.{u}) :
    projectedNativeInclusionIso.inv.app C = Localization.Construction.wInv
      (OriginalBergnerFibrantReplacement.inclusion.app C)
      (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2 := rfl

/-- The same original replacement unit gives a natural isomorphism after categorical localization. -/
def projectedUnitIso : simplicialProjection.{u} ≅
    realizationFunctor.{u} ⋙ nativeReplacedNerve.{u} ⋙ simplicialProjection.{u} :=
  NatIso.ofComponents (fun K => Localization.Construction.wIso
    (OriginalQuillenComparison.replacementUnit.app K)
    (OriginalQuillenComparison.replacementUnit_weak K)) (by
      intro K L f
      exact (Functor.whiskerRight OriginalQuillenComparison.replacementUnit
        simplicialProjection).naturality f)

/-- Its forward component is the image of the same original replacement unit at every source. -/
theorem projectedUnitIso_hom_app (K : SSet.{u}) :
    projectedUnitIso.hom.app K = simplicialProjection.map
      (OriginalQuillenComparison.replacementUnit.app K) := rfl

/-- Its inverse is the formal inverse of the same original weak replacement unit. -/
theorem projectedUnitIso_inv_app (K : SSet.{u}) :
    projectedUnitIso.inv.app K = Localization.Construction.wInv
      (OriginalQuillenComparison.replacementUnit.app K)
      (OriginalQuillenComparison.replacementUnit_weak K) := rfl

/-- The actual original counit on the genuinely locally Kan replacement gives the full forward comparison. -/
def projectedCounitToReplacementIso :
    nativeReplacedNerve.{u} ⋙ realizationFunctor.{u} ⋙ enrichmentProjection.{u} ≅
      OriginalBergnerFibrantReplacement.functor.{u} ⋙ enrichmentProjection.{u} :=
  NatIso.ofComponents (fun C => Localization.Construction.wIso
    (counit (OriginalBergnerFibrantReplacement.functor.obj C))
    (counit_DKweak _ (OriginalBergnerFibrantReplacement.homKan C))) (by
      intro C D F
      exact (Functor.whiskerRight
        (Functor.whiskerLeft OriginalBergnerFibrantReplacement.functor counitNatTrans)
        enrichmentProjection).naturality F)

/-- The reverse localized comparison is the actual counit followed by the inverse native inclusion. -/
def projectedCounitIso :
    nativeReplacedNerve.{u} ⋙ realizationFunctor.{u} ⋙ enrichmentProjection.{u} ≅
      enrichmentProjection.{u} :=
  projectedCounitToReplacementIso ≪≫ projectedNativeInclusionIso.symm

/-- Its whole component is precisely the same original counit/native-inclusion zigzag. -/
theorem projectedCounitIso_hom_app (C : Carrier.{u}) :
    projectedCounitIso.hom.app C =
      enrichmentProjection.map (counit (OriginalBergnerFibrantReplacement.functor.obj C)) ≫
        Localization.Construction.wInv (OriginalBergnerFibrantReplacement.inclusion.app C)
          (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2 := rfl

/-- The reverse component retains the inclusion and the actual formal inverse of the replaced counit. -/
theorem projectedCounitIso_inv_app (C : Carrier.{u}) :
    projectedCounitIso.inv.app C =
      enrichmentProjection.map (OriginalBergnerFibrantReplacement.inclusion.app C) ≫
        Localization.Construction.wInv (counit (OriginalBergnerFibrantReplacement.functor.obj C))
          (counit_DKweak _ (OriginalBergnerFibrantReplacement.homKan C)) := rfl

/-- The localized left triangle is the original replacement-unit factorization followed by the
same inverse inclusion. -/
theorem projected_left_triangle (K : SSet.{u}) :
    left.map (projectedUnitIso.hom.app K) ≫ projectedCounitIso.hom.app (realization K) =
      𝟙 (enrichmentProjection.obj (realization K)) := by
  let η : K ⟶ nativeReplacedNerve.obj (realization K) :=
    OriginalQuillenComparison.replacementUnit.app K
  let δ : realization K ⟶ OriginalBergnerFibrantReplacement.functor.obj (realization K) :=
    OriginalBergnerFibrantReplacement.inclusion.app (realization K)
  let ε : realization (nativeReplacedNerve.obj (realization K)) ⟶
      OriginalBergnerFibrantReplacement.functor.obj (realization K) :=
    counit (OriginalBergnerFibrantReplacement.functor.obj (realization K))
  let i : enrichmentProjection.obj (OriginalBergnerFibrantReplacement.functor.obj (realization K)) ⟶
      enrichmentProjection.obj (realization K) := Localization.Construction.wInv δ
    (OriginalBergnerFibrantReplacement.inclusion_original_classes (realization K)).2
  have hMap : left.map (projectedUnitIso.hom.app K) = enrichmentProjection.map (realizationMap η) :=
    left_map_projection η
  have hCounit : projectedCounitIso.hom.app (realization K) = enrichmentProjection.map ε ≫ i :=
    projectedCounitIso_hom_app (realization K)
  refine (congrArg₂ (fun f g => f ≫ g) hMap hCounit).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun f => f ≫ i) (enrichmentProjection.map_comp (realizationMap η) ε).symm).trans ?_
  refine (congrArg (fun f => enrichmentProjection.map f ≫ i)
    (OriginalQuillenComparison.replacementUnit_counit K)).trans ?_
  exact (Localization.Construction.wIso δ
    (OriginalBergnerFibrantReplacement.inclusion_original_classes (realization K)).2).hom_inv_id

end CategoryTheory.CoherentRealization.OriginalCoherentLocalization
