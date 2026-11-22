/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.FreeWeightedEndMap
public import MathlibExt.Topology.Category.PointedCGWH.EnrichedFunctorMapping
public import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationMappingNormalization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Omega

/-!
# The original native stabilization arrow on full mapping ends

The original free/evaluation adjunct identifies the full mapping-end action
of the literal unit stabilization map. A separate symmetric formula converts
the positive shuffle into the original inverse-braid successor action. The
native application uses the actual symmetry of pointed CGWH spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v uI uV vV

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.FreeWeightedEndMap

section UnitEvaluation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [Closed (𝟙_ V)]

private theorem unitIsoSelf_hom_formula (U : V) :
    (MonoidalClosed.unitIsoSelf U).hom =
      (λ_ ((ihom (𝟙_ V)).obj U)).inv ≫ (ihom.ev (𝟙_ V)).app U := by
  let e := MonoidalClosed.unitIsoSelf U
  have hMate : (𝟙_ V ◁ e.inv) ≫ (ihom.ev (𝟙_ V)).app U = (λ_ U).hom := by
    have h := conjugateEquiv_counit (Adjunction.id (C := V))
      (ihom.adjunction (𝟙_ V)) (leftUnitorNatIso V).hom U
    change (𝟙_ V ◁ (MonoidalClosed.unitNatIso (C := V)).hom.app U) ≫
      (ihom.ev (𝟙_ V)).app U = (λ_ U).hom ≫ 𝟙 U at h
    have hInv : e.inv = (MonoidalClosed.unitNatIso (C := V)).hom.app U := rfl
    rw [← hInv] at h
    exact h.trans (Category.comp_id _)
  apply (cancel_epi e.inv).1
  change e.inv ≫ e.hom = e.inv ≫
    ((λ_ ((ihom (𝟙_ V)).obj U)).inv ≫ (ihom.ev (𝟙_ V)).app U)
  rw [Iso.inv_hom_id, ← Category.assoc, leftUnitor_inv_naturality,
    Category.assoc, hMate, Iso.inv_hom_id]

end UnitEvaluation

section UnitShuffle

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [Closed (𝟙_ V)]

private theorem unit_shuffle_evaluation (H U : V) :
    let T := (ihom (𝟙_ V)).obj U
    ((λ_ H).inv ▷ T) ≫ (α_ (𝟙_ V) H T).hom ≫
        (𝟙_ V ◁ (β_ H T).hom) ≫ (α_ (𝟙_ V) T H).inv ≫
        ((ihom.ev (𝟙_ V)).app U ▷ H) =
      (β_ H T).hom ≫ ((MonoidalClosed.unitIsoSelf U).hom ▷ H) := by
  dsimp only
  let T := (ihom (𝟙_ V)).obj U
  have hLeft : ((λ_ H).inv ▷ T) ≫ (α_ (𝟙_ V) H T).hom = (λ_ (H ⊗ T)).inv :=
    (leftUnitor_tensor_inv H T).symm
  have hMiddle : (λ_ (H ⊗ T)).inv ≫ (𝟙_ V ◁ (β_ H T).hom) =
      (β_ H T).hom ≫ (λ_ (T ⊗ H)).inv :=
    (leftUnitor_inv_naturality (β_ H T).hom).symm
  have hRight : (λ_ (T ⊗ H)).inv ≫ (α_ (𝟙_ V) T H).inv = ((λ_ T).inv ▷ H) :=
    (leftUnitor_inv_whiskerRight T H).symm
  rw [reassoc_of% hLeft, reassoc_of% hMiddle, reassoc_of% hRight,
    ← comp_whiskerRight, ← unitIsoSelf_hom_formula]

end UnitShuffle

section SymmetricUnitTranspose

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

set_option backward.isDefEq.respectTransparency false in
/-- A normalized actual unit free adjunct has the original inverse-braid
transpose under symmetry. -/
theorem transpose_of_normalized_unit_adjunct
    (a b : I) (K : V) (X : EnrichedFunctor V I V)
    (f : EnrichedFunctorCat.Free.object b K ⟶ EnrichedFunctorCat.Free.object a (𝟙_ V))
    (D : K ⟶ (a ⟶[V] b))
    (hAdjunct : (EnrichedFunctorCat.Free.adjunction (V := V) b).homEquiv
      K (EnrichedFunctorCat.Free.object a (𝟙_ V)) f = D ≫ (λ_ (a ⟶[V] b)).inv) :
    transpose a b (𝟙_ V) K X f =
      (MonoidalClosed.unitIsoSelf (X.obj a)).hom ≫ MonoidalClosed.curry
        ((D ▷ X.obj a) ≫ (β_ (X.obj a) (a ⟶[V] b)).inv ≫
          MonoidalClosed.uncurry (X.map a b)) := by
  rw [transpose_eq]
  dsimp only
  rw [hAdjunct]
  let H := a ⟶[V] b
  let U := X.obj a
  let T := (ihom (𝟙_ V)).obj U
  let e := MonoidalClosed.unitIsoSelf U
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% (unit_shuffle_evaluation H U)]
  have hBraid : (β_ H T).hom ≫ (e.hom ▷ H) =
      (H ◁ e.hom) ≫ (β_ H U).hom :=
    (braiding_naturality_right H e.hom).symm
  rw [reassoc_of% hBraid, ← reassoc_of% (whisker_exchange D e.hom)]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding]

end SymmetricUnitTranspose

end CategoryTheory.Enriched.FreeWeightedEndMap

namespace CategoryTheory.Spectra.Sequential

open Limits

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  MonoidalClosed.enrichedCategorySelf

variable {C : Type uV} [Category.{vV} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasInitial C]

set_option backward.isDefEq.respectTransparency false in
/-- The original successor action is the full unit free transpose under actual ambient symmetry. -/
theorem normalizedUnitStabilization_transpose (K : C) (n : ℕ) (X : Spectrum K)
    (f : (freeAt K (n + 1)).obj K ⟶ (freeAt K n).obj (𝟙_ C))
    (hAdjunct : (freeAtEvaluationAdjunction K (n + 1)).homEquiv
      K ((freeAt K n).obj (𝟙_ C)) f =
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv ≫
          (λ_ (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
            (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
            (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)))).inv) :
    Enriched.FreeWeightedEndMap.transpose
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))
        (𝟙_ C) K X.toEnrichedFunctor f =
      (MonoidalClosed.unitIsoSelf (level X n)).hom ≫ adjointStructureMap X n := by
  have h := Enriched.FreeWeightedEndMap.transpose_of_normalized_unit_adjunct
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))
    K X.toEnrichedFunctor f
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv hAdjunct
  dsimp only [adjointStructureMap, structureMap, action, level]
  rw [tensorHom_id]
  convert h using 1

variable (K : C) (n : ℕ) (X : Spectrum K)
  [HasProduct (Enriched.weightedEnd.objects
    ((freeAt K n).obj (𝟙_ C)).toEnrichedFunctor X.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.relations
    ((freeAt K n).obj (𝟙_ C)).toEnrichedFunctor X.toEnrichedFunctor)]
  [HasEqualizer
    (Enriched.weightedEnd.leftMap
      ((freeAt K n).obj (𝟙_ C)).toEnrichedFunctor X.toEnrichedFunctor)
    (Enriched.weightedEnd.rightMap
      ((freeAt K n).obj (𝟙_ C)).toEnrichedFunctor X.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.objects
    ((freeAt K (n + 1)).obj K).toEnrichedFunctor X.toEnrichedFunctor)]
  [HasProduct (Enriched.weightedEnd.relations
    ((freeAt K (n + 1)).obj K).toEnrichedFunctor X.toEnrichedFunctor)]
  [HasEqualizer
    (Enriched.weightedEnd.leftMap
      ((freeAt K (n + 1)).obj K).toEnrichedFunctor X.toEnrichedFunctor)
    (Enriched.weightedEnd.rightMap
      ((freeAt K (n + 1)).obj K).toEnrichedFunctor X.toEnrichedFunctor)]

set_option backward.isDefEq.respectTransparency false in
/-- The original free mapping square retains the actual successor map and only its two ends. -/
theorem normalizedUnitStabilization_mappingSquare
    (f : (freeAt K (n + 1)).obj K ⟶ (freeAt K n).obj (𝟙_ C))
    (hAdjunct : (freeAtEvaluationAdjunction K (n + 1)).homEquiv
      K ((freeAt K n).obj (𝟙_ C)) f =
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv ≫
          (λ_ (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom K
            (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
            (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)))).inv) :
    Enriched.weightedEnd.mapWeight
        ((freeAt K n).obj (𝟙_ C)).toEnrichedFunctor X.toEnrichedFunctor
        ((freeAt K (n + 1)).obj K).toEnrichedFunctor f ≫
        (Enriched.FreeWeightedEnd.iso
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))
          K X.toEnrichedFunctor).hom =
      (Enriched.FreeWeightedEnd.iso
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
        (𝟙_ C) X.toEnrichedFunctor).hom ≫
        (MonoidalClosed.unitIsoSelf (level X n)).hom ≫ adjointStructureMap X n := by
  rw [Enriched.FreeWeightedEnd.iso_hom, Enriched.FreeWeightedEnd.iso_hom]
  have h := Enriched.FreeWeightedEndMap.precomp_forward
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))
    (𝟙_ C) K X.toEnrichedFunctor f
  rw [normalizedUnitStabilization_transpose K n X f hAdjunct] at h
  simpa only [Category.assoc] using h

end CategoryTheory.Spectra.Sequential

namespace PointedCGWH.SequentialSpectrum

open PointedCGWH.EnrichedFunctorMapping

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

set_option backward.isDefEq.respectTransparency false in
/-- The original native free coefficient mapping end has its constructed full evaluation iso. -/
abbrev coordinateFreeMappingIso (K : PointedCGWH.{u, v}) (n : ℕ)
    (A : PointedCGWH.{u, v}) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    mappingObject ((freeAt K n).obj A) X ≅
      (ihom A).obj (CategoryTheory.Spectra.Sequential.level X n) :=
  Enriched.FreeWeightedEnd.iso
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) A X.toEnrichedFunctor

set_option backward.isDefEq.respectTransparency false in
/-- The literal unit stabilization arrow acts through the original full weighted-end source map. -/
abbrev stabilizationMappingArrow (K : PointedCGWH.{u, v}) (n : ℕ)
    (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    mappingObject ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v})) X ⟶
      mappingObject ((freeAt K (n + 1)).obj K) X :=
  Enriched.weightedEnd.mapWeight
    ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v})).toEnrichedFunctor X.toEnrichedFunctor
    ((freeAt K (n + 1)).obj K).toEnrichedFunctor (unitStabilizationMap K n)

set_option backward.isDefEq.respectTransparency false in
/-- The actual native stabilization transpose is the original successor transpose after unit Hom. -/
theorem unitStabilizationMap_mapping_transpose
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    Enriched.FreeWeightedEndMap.transpose
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1))
        (𝟙_ PointedCGWH.{u, v}) K X.toEnrichedFunctor (unitStabilizationMap K n) =
      (MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n)).hom ≫
        CategoryTheory.Spectra.Sequential.adjointStructureMap X n := by
  exact CategoryTheory.Spectra.Sequential.normalizedUnitStabilization_transpose
    K n X (unitStabilizationMap K n)
    (unitStabilizationMap_homEquiv_normalized K n)

set_option backward.isDefEq.respectTransparency false in
/-- Full native precomposition by the original stabilization map is its actual Omega transpose. -/
theorem stabilizationMappingArrow_characteristic
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    stabilizationMappingArrow K n X ≫ (coordinateFreeMappingIso K (n + 1) K X).hom =
      (coordinateFreeMappingIso K n (𝟙_ PointedCGWH.{u, v}) X).hom ≫
        (MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n)).hom ≫
        CategoryTheory.Spectra.Sequential.adjointStructureMap X n := by
  exact CategoryTheory.Spectra.Sequential.normalizedUnitStabilization_mappingSquare
    K n X (unitStabilizationMap K n) (unitStabilizationMap_homEquiv_normalized K n)

set_option backward.isDefEq.respectTransparency false in
/-- The complete original mapping arrow is isomorphic to the actual successor transpose in Arrow. -/
@[no_expose]
def stabilizationMappingArrowIso
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    Arrow.mk (stabilizationMappingArrow K n X) ≅
      Arrow.mk (CategoryTheory.Spectra.Sequential.adjointStructureMap X n) :=
  Arrow.isoMk' (stabilizationMappingArrow K n X)
    (CategoryTheory.Spectra.Sequential.adjointStructureMap X n)
    (coordinateFreeMappingIso K n (𝟙_ PointedCGWH.{u, v}) X ≪≫
      MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n))
    (coordinateFreeMappingIso K (n + 1) K X)
    (by simpa only [Iso.trans_hom, Category.assoc] using
      (stabilizationMappingArrow_characteristic K n X).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem stabilizationMappingArrowIso_hom_left_private
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).hom.left =
      (coordinateFreeMappingIso K n (𝟙_ PointedCGWH.{u, v}) X).hom ≫
        (MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole Arrow comparison retains free-unit evaluation and the original unit Hom iso. -/
theorem stabilizationMappingArrowIso_hom_left
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).hom.left =
      (coordinateFreeMappingIso K n (𝟙_ PointedCGWH.{u, v}) X).hom ≫
        (MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n)).hom :=
  stabilizationMappingArrowIso_hom_left_private K n X

set_option backward.isDefEq.respectTransparency false in
private theorem stabilizationMappingArrowIso_hom_right_private
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).hom.right =
      (coordinateFreeMappingIso K (n + 1) K X).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole Arrow comparison retains the actual successor free-unit evaluation. -/
theorem stabilizationMappingArrowIso_hom_right
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).hom.right =
      (coordinateFreeMappingIso K (n + 1) K X).hom :=
  stabilizationMappingArrowIso_hom_right_private K n X

set_option backward.isDefEq.respectTransparency false in
private theorem stabilizationMappingArrowIso_inv_left_private
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).inv.left =
      (MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n)).inv ≫
        (coordinateFreeMappingIso K n (𝟙_ PointedCGWH.{u, v}) X).inv := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse source map retains both original chosen inverse maps. -/
theorem stabilizationMappingArrowIso_inv_left
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).inv.left =
      (MonoidalClosed.unitIsoSelf (CategoryTheory.Spectra.Sequential.level X n)).inv ≫
        (coordinateFreeMappingIso K n (𝟙_ PointedCGWH.{u, v}) X).inv :=
  stabilizationMappingArrowIso_inv_left_private K n X

set_option backward.isDefEq.respectTransparency false in
private theorem stabilizationMappingArrowIso_inv_right_private
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).inv.right =
      (coordinateFreeMappingIso K (n + 1) K X).inv := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse target map retains the complete original free-end reconstruction. -/
theorem stabilizationMappingArrowIso_inv_right
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    (stabilizationMappingArrowIso K n X).inv.right =
      (coordinateFreeMappingIso K (n + 1) K X).inv :=
  stabilizationMappingArrowIso_inv_right_private K n X

set_option backward.isDefEq.respectTransparency false in
/-- Every isomorphism-invariant native arrow class detects the exact original successor map. -/
theorem stabilizationMappingArrow_property_iff
    (W : MorphismProperty PointedCGWH.{u, v}) [W.RespectsIso]
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    W (stabilizationMappingArrow K n X) ↔
      W (CategoryTheory.Spectra.Sequential.adjointStructureMap X n) :=
  W.arrow_mk_iso_iff (stabilizationMappingArrowIso K n X)

set_option backward.isDefEq.respectTransparency false in
/-- The original native mapping-end test detects the actual successor weak equivalence. -/
theorem stabilizationMappingArrow_weak_iff
    (K : PointedCGWH.{u, v}) (n : ℕ) (X : CategoryTheory.Spectra.Sequential.Spectrum K) :
    CGWH.weakHomotopyEquivalences (stabilizationMappingArrow K n X).right ↔
      CGWH.weakHomotopyEquivalences
        (CategoryTheory.Spectra.Sequential.adjointStructureMap X n).right := by
  let _ : (CGWH.weakHomotopyEquivalences.{u, v}.inverseImage
      PointedCGWH.pointedToCGWH).RespectsIso := by
    unfold CGWH.weakHomotopyEquivalences CompactlyGenerated.weakHomotopyEquivalences
    infer_instance
  exact stabilizationMappingArrow_property_iff
    (CGWH.weakHomotopyEquivalences.inverseImage PointedCGWH.pointedToCGWH) K n X

set_option backward.isDefEq.respectTransparency false in
/-- The actual native Omega predicate is exactly the full original strict mapping-end tests. -/
theorem isOmega_iff_stabilizationMappingArrows (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    X.IsOmega ↔ ∀ n : ℕ,
      CGWH.weakHomotopyEquivalences
        (stabilizationMappingArrow PointedCGWH.sphereOne n X).right := by
  rw [isOmega_iff]
  exact forall_congr' fun n =>
    (stabilizationMappingArrow_weak_iff PointedCGWH.sphereOne n X).symm

end PointedCGWH.SequentialSpectrum
