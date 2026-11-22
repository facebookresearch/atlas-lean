/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Native TCof/Fib rectification; no diagonal fibration or completion outcome is assumed.
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFibreCoverageFiniteBase
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback

/-!
# Rectifying comparisons over a fibration

A simplicial map is factored as a trivial cofibration followed by a fibration, retaining its original composite over the base. When the target projection is a fibration, component coverage and realization weak equivalences of the rectified image fibres imply weakness of the original map; the prefix also induces a weak map on the corresponding homotopy point pullbacks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-- Rectify the original comparison itself, using the actual native factorization. -/
def coreComparisonFactorization {X Y : SSet.{u}} (c : X ⟶ Y) :
    MorphismProperty.MapFactorizationData
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) c :=
  MorphismProperty.factorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) c

/-- Its source and target base maps are the SAME original map and the target
projection after the actual fibration factor. -/
def rectifiedCoreBase {X Y B : SSet.{u}} (c : X ⟶ Y) (t : Y ⟶ B) :
    (coreComparisonFactorization c).Z ⟶ B :=
  (coreComparisonFactorization c).p ≫ t

/-- The actual trivial cofibration factor commutes with the original base map. -/
theorem coreComparisonFactorization_over_base
    {X Y B : SSet.{u}} (c : X ⟶ Y) (t : Y ⟶ B) :
    (coreComparisonFactorization c).i ≫ rectifiedCoreBase c t = c ≫ t := by
  rw [rectifiedCoreBase, ← Category.assoc, (coreComparisonFactorization c).fac]

/-- The rectified comparison and its actual base projection are fibrations
when the original target core endpoint projection is one. -/
theorem coreComparisonFactorization_fibrations
    {X Y B : SSet.{u}} (c : X ⟶ Y) (t : Y ⟶ B) [Fibration t] :
    Fibration (coreComparisonFactorization c).p ∧
      Fibration (rectifiedCoreBase c t) := by
  let : Fibration (coreComparisonFactorization c).p :=
    (fibration_iff _).mpr (coreComparisonFactorization c).hp
  exact ⟨inferInstance, by dsimp only [rectifiedCoreBase]; infer_instance⟩

/-- The whole original comparison has a genuine weak trivial-cofibration prefix. -/
theorem coreComparisonFactorization_prefix_weak
    {X Y : SSet.{u}} (c : X ⟶ Y) :
    realizationWeakEquivalences (coreComparisonFactorization c).i :=
  (weakEquivalence_iff _).mp
    ((mem_trivialCofibrations_iff _).mp (coreComparisonFactorization c).hi).2

private def originalPointCospan {X B : SSet.{u}} (s : X ⟶ B)
    (b : (Δ[0] : SSet.{u}) ⟶ B) : WalkingCospan ⥤ SSet.{u} := cospan s b

private def factorPrefixPointCospanMap {X Y B : SSet.{u}}
    (c : X ⟶ Y) (t : Y ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    originalPointCospan (c ≫ t) b ⟶
      originalPointCospan (rectifiedCoreBase c t) b :=
  cospanHomMk (𝟙 B) (coreComparisonFactorization c).i (𝟙 (Δ[0] : SSet.{u}))
    (by
      change (c ≫ t) ≫ 𝟙 B = (coreComparisonFactorization c).i ≫ rectifiedCoreBase c t
      simpa only [Category.comp_id] using (coreComparisonFactorization_over_base c t).symm)
    (by
      change b ≫ 𝟙 B = 𝟙 (Δ[0] : SSet.{u}) ≫ b
      simp only [Category.comp_id, Category.id_comp])

/-- The actual native HP map of the rectification prefix is weak, even when
the original diagonal-to-base projection is not a fibration. -/
theorem rectification_prefix_homotopyPointMap_weak
    {X Y B : SSet.{u}} (c : X ⟶ Y) (t : Y ⟶ B)
    (b : (Δ[0] : SSet.{u}) ⟶ B) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (cospanHomMk (F := cospan (c ≫ t) b)
        (G := cospan (rectifiedCoreBase c t) b) (𝟙 B) (coreComparisonFactorization c).i
        (𝟙 (Δ[0] : SSet.{u}))
        (by
      change (c ≫ t) ≫ 𝟙 B = (coreComparisonFactorization c).i ≫ rectifiedCoreBase c t
      simpa only [Category.comp_id] using (coreComparisonFactorization_over_base c t).symm)
        (by
      change b ≫ 𝟙 B = 𝟙 (Δ[0] : SSet.{u}) ≫ b
      simp only [Category.comp_id, Category.id_comp]))) := by
  apply homotopyPullback_map_weakEquivalence
  intro j
  cases j with
  | none => exact inferInstanceAs (WeakEquivalence (𝟙 B))
  | some pair =>
      cases pair with
      | left => exact (weakEquivalence_iff _).mpr (coreComparisonFactorization_prefix_weak c)
      | right => exact inferInstanceAs (WeakEquivalence (𝟙 (Δ[0] : SSet.{u})))

/-- A generic rectified comparison is globally weak once its actual image
point-fibre comparisons have been derived over component-covering base data.
This does not assume the original diagonal projection or c is a fibration. -/
theorem originalCoreComparison_weak_of_rectified_image_fibres
    {A X Y B : SSet.{u}} (a : A ⟶ B) (c : X ⟶ Y) (t : Y ⟶ B)
    [Fibration t]
    (ha : Function.Surjective (SSet.mapπ₀ a))
    (himage : ∀ x : A _⦋0⦌, realizationWeakEquivalences
      (sameBasePullbackComparison (coreComparisonFactorization c).p
        (rectifiedCoreBase c t) t rfl
        (SSet.yonedaEquiv.symm (a.app (op ⦋0⦌) x)))) :
    realizationWeakEquivalences c := by
  let : Fibration (coreComparisonFactorization c).p :=
    (coreComparisonFactorization_fibrations c t).1
  let : Fibration (rectifiedCoreBase c t) :=
    (coreComparisonFactorization_fibrations c t).2
  have hp : realizationWeakEquivalences (coreComparisonFactorization c).p :=
    realizationWeakEquivalence_of_image_fibres_component_coverage
      a (coreComparisonFactorization c).p (rectifiedCoreBase c t) t rfl ha himage
  simpa only [(coreComparisonFactorization c).fac] using
    realizationWeakEquivalences.comp_mem
      (coreComparisonFactorization c).i (coreComparisonFactorization c).p
      (coreComparisonFactorization_prefix_weak c) hp

end SSet
