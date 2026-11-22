/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentLocalizationZigzag

/-!
# The original coherent adjunction induces an ordinary localization equivalence

The original weak replacement unit and counit/native-inclusion zigzag
descend to natural isomorphisms for the two actual localization functors.
Their components retain the projected original maps and formal inverses.
The triangle is proved from the original replacement-unit factorization,
so the equivalence uses these same unit and counit isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalCoherentLocalization

open SimplicialEnrichment

private instance simplicialProjection_isLocalization :
    simplicialProjection.{u}.IsLocalization SSet.categoricalEquivalences.{u} := by
  change SSet.categoricalEquivalences.{u}.Q.IsLocalization SSet.categoricalEquivalences.{u}
  infer_instance

private instance enrichmentProjection_isLocalization :
    enrichmentProjection.{u}.IsLocalization EnrichedDwyerKan.weakEquivalences.{u} := by
  change EnrichedDwyerKan.weakEquivalences.{u}.Q.IsLocalization EnrichedDwyerKan.weakEquivalences.{u}
  infer_instance

/-- The actual left/right composite retains the same projected native-replaced realization route. -/
theorem leftRight_fac : simplicialProjection.{u} ⋙ (left.{u} ⋙ right.{u}) =
    realizationFunctor.{u} ⋙ nativeReplacedNerve.{u} ⋙ simplicialProjection.{u} := by
  calc
    simplicialProjection ⋙ (left ⋙ right) = (simplicialProjection ⋙ left) ⋙ right := rfl
    _ = (realizationFunctor ⋙ enrichmentProjection) ⋙ right :=
      congrArg (fun F => F ⋙ right) left_fac
    _ = realizationFunctor ⋙ (enrichmentProjection ⋙ right) := rfl
    _ = realizationFunctor ⋙ (nativeReplacedNerve ⋙ simplicialProjection) :=
      congrArg (fun F => realizationFunctor ⋙ F) right_fac

/-- The actual right/left composite retains the same projected counit route. -/
theorem rightLeft_fac : enrichmentProjection.{u} ⋙ (right.{u} ⋙ left.{u}) =
    nativeReplacedNerve.{u} ⋙ realizationFunctor.{u} ⋙ enrichmentProjection.{u} := by
  calc
    enrichmentProjection ⋙ (right ⋙ left) = (enrichmentProjection ⋙ right) ⋙ left := rfl
    _ = (nativeReplacedNerve ⋙ simplicialProjection) ⋙ left :=
      congrArg (fun F => F ⋙ left) right_fac
    _ = nativeReplacedNerve ⋙ (simplicialProjection ⋙ left) := rfl
    _ = nativeReplacedNerve ⋙ (realizationFunctor ⋙ enrichmentProjection) :=
      congrArg (fun F => nativeReplacedNerve ⋙ F) left_fac

private instance leftRight_lifting : Localization.Lifting simplicialProjection.{u}
    SSet.categoricalEquivalences.{u}
    (realizationFunctor.{u} ⋙ nativeReplacedNerve.{u} ⋙ simplicialProjection.{u})
    (left.{u} ⋙ right.{u}) := ⟨eqToIso leftRight_fac⟩

private instance rightLeft_lifting : Localization.Lifting enrichmentProjection.{u}
    EnrichedDwyerKan.weakEquivalences.{u}
    (nativeReplacedNerve.{u} ⋙ realizationFunctor.{u} ⋙ enrichmentProjection.{u})
    (right.{u} ⋙ left.{u}) := ⟨eqToIso rightLeft_fac⟩

/-- The unit of the ordinary localization equivalence descends from the actual original replacement unit. -/
def unitIso : 𝟭 simplicialLocalization.{u} ≅ left.{u} ⋙ right.{u} :=
  Localization.liftNatIso simplicialProjection SSet.categoricalEquivalences
    simplicialProjection (realizationFunctor ⋙ nativeReplacedNerve ⋙ simplicialProjection)
    (𝟭 simplicialLocalization) (left ⋙ right) projectedUnitIso

/-- The counit descends from the actual original counit/native-inclusion zigzag. -/
def counitIso : right.{u} ⋙ left.{u} ≅ 𝟭 enrichmentLocalization.{u} :=
  Localization.liftNatIso enrichmentProjection EnrichedDwyerKan.weakEquivalences
    (nativeReplacedNerve ⋙ realizationFunctor ⋙ enrichmentProjection) enrichmentProjection
    (right ⋙ left) (𝟭 enrichmentLocalization) projectedCounitIso

/-- Every original source retains the same projected replacement-unit component. -/
theorem unitIso_hom_projection (K : SSet.{u}) :
    unitIso.hom.app (simplicialProjection.obj K) =
      simplicialProjection.map (OriginalQuillenComparison.replacementUnit.app K) := by
  have h := Localization.liftNatTrans_app simplicialProjection SSet.categoricalEquivalences
    simplicialProjection (realizationFunctor ⋙ nativeReplacedNerve ⋙ simplicialProjection)
    (𝟭 simplicialLocalization) (left ⋙ right) projectedUnitIso.hom K
  refine h.trans ?_
  change (𝟙 _) ≫ simplicialProjection.map (OriginalQuillenComparison.replacementUnit.app K) ≫ (𝟙 _) =
    simplicialProjection.map (OriginalQuillenComparison.replacementUnit.app K)
  simp only [Category.id_comp, Category.comp_id]

/-- Every inverse unit component is the same formal inverse of the original weak replacement unit. -/
theorem unitIso_inv_projection (K : SSet.{u}) :
    unitIso.inv.app (simplicialProjection.obj K) = Localization.Construction.wInv
      (OriginalQuillenComparison.replacementUnit.app K)
      (OriginalQuillenComparison.replacementUnit_weak K) := by
  have h := Localization.liftNatTrans_app simplicialProjection SSet.categoricalEquivalences
    (realizationFunctor ⋙ nativeReplacedNerve ⋙ simplicialProjection) simplicialProjection
    (left ⋙ right) (𝟭 simplicialLocalization) projectedUnitIso.inv K
  refine h.trans ?_
  change (𝟙 _) ≫ Localization.Construction.wInv
    (OriginalQuillenComparison.replacementUnit.app K)
    (OriginalQuillenComparison.replacementUnit_weak K) ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Every original enrichment retains the actual projected counit followed by the inverse native inclusion. -/
theorem counitIso_hom_projection (C : Carrier.{u}) :
    counitIso.hom.app (enrichmentProjection.obj C) =
      enrichmentProjection.map (counit (OriginalBergnerFibrantReplacement.functor.obj C)) ≫
        Localization.Construction.wInv (OriginalBergnerFibrantReplacement.inclusion.app C)
          (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2 := by
  have h := Localization.liftNatTrans_app enrichmentProjection EnrichedDwyerKan.weakEquivalences
    (nativeReplacedNerve ⋙ realizationFunctor ⋙ enrichmentProjection) enrichmentProjection
    (right ⋙ left) (𝟭 enrichmentLocalization) projectedCounitIso.hom C
  refine h.trans ?_
  change (𝟙 _) ≫ (enrichmentProjection.map
    (counit (OriginalBergnerFibrantReplacement.functor.obj C)) ≫
      Localization.Construction.wInv (OriginalBergnerFibrantReplacement.inclusion.app C)
        (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2) ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Every inverse counit component retains the inclusion and the formal inverse of the same replaced counit. -/
theorem counitIso_inv_projection (C : Carrier.{u}) :
    counitIso.inv.app (enrichmentProjection.obj C) =
      enrichmentProjection.map (OriginalBergnerFibrantReplacement.inclusion.app C) ≫
        Localization.Construction.wInv (counit (OriginalBergnerFibrantReplacement.functor.obj C))
          (counit_DKweak _ (OriginalBergnerFibrantReplacement.homKan C)) := by
  have h := Localization.liftNatTrans_app enrichmentProjection EnrichedDwyerKan.weakEquivalences
    enrichmentProjection (nativeReplacedNerve ⋙ realizationFunctor ⋙ enrichmentProjection)
    (𝟭 enrichmentLocalization) (right ⋙ left) projectedCounitIso.inv C
  refine h.trans ?_
  change (𝟙 _) ≫ (enrichmentProjection.map (OriginalBergnerFibrantReplacement.inclusion.app C) ≫
    Localization.Construction.wInv (counit (OriginalBergnerFibrantReplacement.functor.obj C))
      (counit_DKweak _ (OriginalBergnerFibrantReplacement.homKan C))) ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

private theorem sourceProjection_obj_surjective : Function.Surjective simplicialProjection.{u}.obj := by
  rintro ⟨⟨K⟩⟩
  exact ⟨K, rfl⟩

/-- The actual original coherent realization and native-replaced nerve induce an ordinary localization equivalence. -/
def equivalence : simplicialLocalization.{u} ≌ enrichmentLocalization.{u} where
  functor := left
  inverse := right
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp X := by
    obtain ⟨K, rfl⟩ := sourceProjection_obj_surjective X
    exact (congrArg₂ (fun f g => left.map f ≫ g) (unitIso_hom_projection K)
      (counitIso_hom_projection (realization K))).trans (projected_left_triangle K)

end CategoryTheory.CoherentRealization.OriginalCoherentLocalization
