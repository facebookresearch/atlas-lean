/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.WeakArrowAccessibility
import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.LiftingTest
import MathlibExt.CategoryTheory.Presentable.LiftingTest
import MathlibExt.CategoryTheory.Presentable.FunctorCategory

/-!
# The original diagram weak-equivalence test

Every representative evaluation uses the same original base J right factor
and the original I lifting test. The fixed tagged collection and its
working-size normalization retain all original component functions.
Actual index unit/counit isomorphisms detect every original diagram object.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uS vS uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.MorphismProperty.LiftingTest

namespace HomotopicalAlgebra

variable (D : Type uD) [Category.{vD} D] (C : Type uC) [Category.{vC} C]
  [ModelCategory C]

/-- Compatibility name for the canonical property of original objectwise weak arrows. -/
abbrev functorModelWeakArrows : ObjectProperty (Arrow (D ⥤ C)) :=
  ((weakEquivalences C).functorCategory D).arrowObjectProperty

/-- Compatibility name used by the original diagram weak-arrow solution families. -/
abbrev FunctorModelWeakArrow :=
  ((weakEquivalences C).functorCategory D).arrowObjectProperty.FullSubcategory

/-- Original diagram Arrow isomorphisms preserve the canonical objectwise weak property. -/
instance instIsClosedUnderIsomorphismsArrowFunctorFunctorModelWeakArrows :
    ((weakEquivalences C).functorCategory D).arrowObjectProperty.IsClosedUnderIsomorphisms where
  of_iso e hp := ((weakEquivalences C).functorCategory D).arrow_mk_iso_iff e |>.mp hp

end HomotopicalAlgebra

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (e : D ≌ S)

/-- Each original representative uses its actual evaluation and same base weak test. -/
def functorWeakComponent (s : S) : Arrow (D ⥤ C) ⥤ Arrow (Type w) :=
  Functor.mapArrow ((evaluation D C).obj (e.inverse.obj s)) ⋙ d.weakLiftingTest

/-- The raw collection keeps every original representative and actual component test value. -/
def functorWeakCollection : Arrow (D ⥤ C) ⥤ Arrow (Type (max uS w)) :=
  collectionFunctor (d.functorWeakComponent e)

/-- The entire raw object function retains the representative and actual component test. -/
theorem functorWeakCollection_hom_function (p : Arrow (D ⥤ C)) :
    ((d.functorWeakCollection e).obj p).hom =
      TypeCat.ofHom (fun z : CollectionLeft (d.functorWeakComponent e) p ↦
        (⟨z.1, ((d.functorWeakComponent e z.1).obj p).hom z.2⟩ :
          CollectionRight (d.functorWeakComponent e) p)) :=
  collectionFunctor_hom_function (d.functorWeakComponent e) p

/-- Every raw source map retains the same representative and actual component source map. -/
theorem functorWeakCollection_map_left_function
    {p q : Arrow (D ⥤ C)} (τ : p ⟶ q) :
    ((d.functorWeakCollection e).map τ).left =
      TypeCat.ofHom (fun z : CollectionLeft (d.functorWeakComponent e) p ↦
        (⟨z.1, ((d.functorWeakComponent e z.1).map τ).left z.2⟩ :
          CollectionLeft (d.functorWeakComponent e) q)) :=
  collectionFunctor_map_left_function (d.functorWeakComponent e) τ

/-- Every raw target map retains the same representative and actual component square map. -/
theorem functorWeakCollection_map_right_function
    {p q : Arrow (D ⥤ C)} (τ : p ⟶ q) :
    ((d.functorWeakCollection e).map τ).right =
      TypeCat.ofHom (fun z : CollectionRight (d.functorWeakComponent e) p ↦
        (⟨z.1, ((d.functorWeakComponent e z.1).map τ).right z.2⟩ :
          CollectionRight (d.functorWeakComponent e) q)) :=
  collectionFunctor_map_right_function (d.functorWeakComponent e) τ

section WorkingSize

variable [Small.{w} S]

/-- The whole original representative source family is working-small. -/
instance functorWeakCollection_left_small (p : Arrow (D ⥤ C)) :
    Small.{w} ((d.functorWeakCollection e).obj p).left := by
  change Small.{w} (Σ s : S, ((d.functorWeakComponent e s).obj p).left)
  infer_instance

/-- The whole original representative target family is working-small. -/
instance functorWeakCollection_right_small (p : Arrow (D ⥤ C)) :
    Small.{w} ((d.functorWeakCollection e).obj p).right := by
  change Small.{w} (Σ s : S, ((d.functorWeakComponent e s).obj p).right)
  infer_instance

/-- Normalize only the actual original collected source and target element families. -/
def functorWeakLiftingTest : Arrow (D ⥤ C) ⥤ Arrow (Type w) := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  exact normalizedFunctor.{w} (d.functorWeakCollection e)

/-- The entire normalized object function retains the actual raw representative collection. -/
theorem functorWeakLiftingTest_hom_function (p : Arrow (D ⥤ C)) :
    ((d.functorWeakLiftingTest e).obj p).hom ∘
        equivShrink.{w} ((d.functorWeakCollection e).obj p).left =
      equivShrink.{w} ((d.functorWeakCollection e).obj p).right ∘
        ((d.functorWeakCollection e).obj p).hom := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  exact normalizedFunctor_hom_function.{w} (d.functorWeakCollection e) p

/-- The entire normalized source map keeps the original representative and component source map. -/
theorem functorWeakLiftingTest_map_left_function
    {p q : Arrow (D ⥤ C)} (τ : p ⟶ q) :
    ((d.functorWeakLiftingTest e).map τ).left ∘
        equivShrink.{w} ((d.functorWeakCollection e).obj p).left =
      equivShrink.{w} ((d.functorWeakCollection e).obj q).left ∘
        ((d.functorWeakCollection e).map τ).left := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  exact normalizedFunctor_map_left_function.{w} (d.functorWeakCollection e) τ

/-- The entire normalized target map keeps the original representative and component square map. -/
theorem functorWeakLiftingTest_map_right_function
    {p q : Arrow (D ⥤ C)} (τ : p ⟶ q) :
    ((d.functorWeakLiftingTest e).map τ).right ∘
        equivShrink.{w} ((d.functorWeakCollection e).obj p).right =
      equivShrink.{w} ((d.functorWeakCollection e).obj q).right ∘
        ((d.functorWeakCollection e).map τ).right := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  exact normalizedFunctor_map_right_function.{w} (d.functorWeakCollection e) τ

/-- Decoding the entire normalized object function recovers the actual raw collection. -/
theorem functorWeakLiftingTest_decoded_hom_function (p : Arrow (D ⥤ C)) :
    (equivShrink.{w} ((d.functorWeakCollection e).obj p).right).symm ∘
        ((d.functorWeakLiftingTest e).obj p).hom =
      ((d.functorWeakCollection e).obj p).hom ∘
        (equivShrink.{w} ((d.functorWeakCollection e).obj p).left).symm := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  funext z
  exact (equivShrink.{w} ((d.functorWeakCollection e).obj p).right).symm_apply_apply _

/-- Decoding the entire normalized source map retains every original collection value. -/
theorem functorWeakLiftingTest_decoded_map_left_function
    {p q : Arrow (D ⥤ C)} (τ : p ⟶ q) :
    (equivShrink.{w} ((d.functorWeakCollection e).obj q).left).symm ∘
        ((d.functorWeakLiftingTest e).map τ).left =
      ((d.functorWeakCollection e).map τ).left ∘
        (equivShrink.{w} ((d.functorWeakCollection e).obj p).left).symm := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  funext z
  exact (equivShrink.{w} ((d.functorWeakCollection e).obj q).left).symm_apply_apply _

/-- Decoding the entire normalized target map retains every original collection square. -/
theorem functorWeakLiftingTest_decoded_map_right_function
    {p q : Arrow (D ⥤ C)} (τ : p ⟶ q) :
    (equivShrink.{w} ((d.functorWeakCollection e).obj q).right).symm ∘
        ((d.functorWeakLiftingTest e).map τ).right =
      ((d.functorWeakCollection e).map τ).right ∘
        (equivShrink.{w} ((d.functorWeakCollection e).obj p).right).symm := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  funext z
  exact (equivShrink.{w} ((d.functorWeakCollection e).obj q).right).symm_apply_apply _

/-- The same actual diagram tester detects weakness at every ORIGINAL diagram object. -/
theorem functorWeakLiftingTest_surjective_iff (p : Arrow (D ⥤ C)) :
    Function.Surjective ((d.functorWeakLiftingTest e).obj p).hom ↔
      (weakEquivalences C).functorCategory D p.hom := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).left :=
    d.functorWeakCollection_left_small e
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((d.functorWeakCollection e).obj p).right :=
    d.functorWeakCollection_right_small e
  rw [show d.functorWeakLiftingTest e = normalizedFunctor.{w}
    (d.functorWeakCollection e) from rfl, normalizedFunctor_surjective_iff]
  rw [show d.functorWeakCollection e =
    collectionFunctor (d.functorWeakComponent e) from rfl, collectionFunctor_surjective_iff]
  rw [← functorCategory_inverseImage_congrLeft e (weakEquivalences C)]
  change (∀ s : S, Function.Surjective
    (d.weakLiftingTest.obj (Arrow.mk (p.hom.app (e.inverse.obj s)))).hom) ↔
      ∀ s : S, weakEquivalences C (p.hom.app (e.inverse.obj s))
  exact forall_congr' (fun s ↦ d.weakLiftingTest_surjective_iff
    (Arrow.mk (p.hom.app (e.inverse.obj s))))

section FixedRank

variable [HasColimitsOfSize.{w, w} C] (χ : Cardinal.{w}) [Fact χ.IsRegular]
  [∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ]
  [∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ]
  [∀ j : d.J.toSet, IsCardinalPresentable j.1.left χ]
  [∀ j : d.J.toSet, IsCardinalPresentable j.1.right χ]

omit [Small.{w} S] in
/-- Every same original representative component derives preservation at the actual rank. -/
theorem functorWeakComponent_isCardinalAccessible (s : S) :
    (d.functorWeakComponent e s).IsCardinalAccessible χ := by
  let _ : (Functor.mapArrow ((evaluation D C).obj (e.inverse.obj s))).IsCardinalAccessible χ :=
    CategoryTheory.Presentable.LiftingTest.evaluationArrow_isCardinalAccessible
      (e.inverse.obj s) χ
  let _ : d.weakLiftingTest.IsCardinalAccessible χ := d.weakLiftingTest_isCardinalAccessible χ
  change (Functor.mapArrow ((evaluation D C).obj (e.inverse.obj s)) ⋙
    d.weakLiftingTest).IsCardinalAccessible χ
  infer_instance

omit [Small.{w} S] in
/-- The actual fixed representative collection preserves without a tag bound below χ. -/
theorem functorWeakCollection_isCardinalAccessible :
    (d.functorWeakCollection e).IsCardinalAccessible χ := by
  let (s : S) : (d.functorWeakComponent e s).IsCardinalAccessible χ :=
    d.functorWeakComponent_isCardinalAccessible e χ s
  let _ : (Arrow.leftFunc : Arrow (Type w) ⥤ Type w).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.fst (𝟭 (Type w)) (𝟭 (Type w))).IsCardinalAccessible χ)
  let _ : (Arrow.rightFunc : Arrow (Type w) ⥤ Type w).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.snd (𝟭 (Type w)) (𝟭 (Type w))).IsCardinalAccessible χ)
  let (s : S) : (d.functorWeakComponent e s ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    inferInstance
  let (s : S) : (d.functorWeakComponent e s ⋙ Arrow.rightFunc).IsCardinalAccessible χ :=
    inferInstance
  exact CategoryTheory.Presentable.LiftingTest.collection_isCardinalAccessible
    (d.functorWeakComponent e) χ

/-- Both original collection projections derive preservation of the actual normalized tester. -/
theorem functorWeakLiftingTest_isCardinalAccessible :
    (d.functorWeakLiftingTest e).IsCardinalAccessible χ := by
  let _ : (d.functorWeakCollection e).IsCardinalAccessible χ :=
    d.functorWeakCollection_isCardinalAccessible e χ
  let _ : (Arrow.leftFunc : Arrow (Type (max uS w)) ⥤ Type (max uS w)).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.fst (𝟭 (Type (max uS w))) (𝟭 (Type (max uS w)))).IsCardinalAccessible χ)
  let _ : (Arrow.rightFunc : Arrow (Type (max uS w)) ⥤ Type (max uS w)).IsCardinalAccessible χ :=
    inferInstanceAs ((Comma.snd (𝟭 (Type (max uS w))) (𝟭 (Type (max uS w)))).IsCardinalAccessible χ)
  let _ : (d.functorWeakCollection e ⋙ Arrow.leftFunc).IsCardinalAccessible χ := inferInstance
  let _ : (d.functorWeakCollection e ⋙ Arrow.rightFunc).IsCardinalAccessible χ := inferInstance
  change (normalizedFunctor.{w} (d.functorWeakCollection e)).IsCardinalAccessible χ
  exact CategoryTheory.Presentable.LiftingTest.normalized_isCardinalAccessible
    (d.functorWeakCollection e) χ

end FixedRank

end WorkingSize

include d in
omit e in
/-- The actual diagram weak category and its inclusion have a genuinely produced regular rank. -/
theorem functorWeakEquivalences_accessible
    (s : Functor.EssentialIndexData.{w} D C)
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      ((weakEquivalences C).functorCategory D).IsCardinalAccessible ν := by
  let _ : SmallCategory s.index := s.indexCategory
  let _ : Small.{w} s.index := inferInstance
  let _ : IsCardinalLocallyPresentable (D ⥤ C) κLP :=
    s.isCardinalLocallyPresentable κLP
  let _ : IsAccessibleCategory.{w} (Arrow (D ⥤ C)) :=
    ⟨κLP, inferInstance, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (Arrow (Type w)) :=
    ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩
  obtain ⟨χ, hχ, _hω, _hLP, _hκ, hC, hI, hJ,
      _hIZ, _hJZ, _hIL, _hIR, _hJL, _hJR, _hTest⟩ :=
    d.exists_common_weak_test_accessibility_cardinal κLP
  let _ : Fact χ.IsRegular := hχ
  let _ : IsCardinalLocallyPresentable C χ := hC
  let _ : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ := fun i ↦ (hI i).1
  let _ : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ := fun i ↦ (hI i).2
  let _ : ∀ j : d.J.toSet, IsCardinalPresentable j.1.left χ := fun j ↦ (hJ j).1
  let _ : ∀ j : d.J.toSet, IsCardinalPresentable j.1.right χ := fun j ↦ (hJ j).2
  let _ : (d.functorWeakLiftingTest s.equivalence).IsCardinalAccessible χ :=
    d.functorWeakLiftingTest_isCardinalAccessible s.equivalence χ
  let _ : Functor.IsAccessible.{w} (d.functorWeakLiftingTest s.equivalence) :=
    Functor.isAccessible_of_isCardinalAccessible _ χ
  obtain ⟨hSurjective, hInclusion⟩ := CategoryTheory.Presentable.surjectiveArrow_accessible.{w}
  let _ : IsAccessibleCategory.{w} CategoryTheory.Presentable.SurjectiveArrow.{w} := hSurjective
  let _ : Functor.IsAccessible.{w} CategoryTheory.Presentable.surjectiveArrows.{w}.ι := hInclusion
  have hProperty : ((weakEquivalences C).functorCategory D).arrowObjectProperty =
      CategoryTheory.Presentable.surjectiveArrows.{w}.inverseImage
        (d.functorWeakLiftingTest s.equivalence) := by
    funext p
    exact propext (d.functorWeakLiftingTest_surjective_iff s.equivalence p).symm
  obtain ⟨ν, hν, hCategory, hι⟩ := CategoryTheory.Presentable.inverseImage_accessible
    (d.functorWeakLiftingTest s.equivalence) CategoryTheory.Presentable.surjectiveArrows.{w}
  let _ : Fact ν.IsRegular := hν
  refine ⟨ν, hν, ?_⟩
  constructor
  · change IsCardinalAccessibleCategory
      ((weakEquivalences C).functorCategory D).arrowObjectProperty.FullSubcategory ν
    rw [hProperty]
    exact hCategory
  · rw [hProperty]
    exact hι

include d in
omit e in
/-- The original objectwise weak-equivalence morphism property has its produced rank. -/
theorem functorWeakEquivalences_isAccessible
    (s : Functor.EssentialIndexData.{w} D C)
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    MorphismProperty.IsAccessible.{w} ((weakEquivalences C).functorCategory D) := by
  obtain ⟨ν, hν, hW⟩ := d.functorWeakEquivalences_accessible s κLP
  exact ⟨ν, hν, hW⟩

include d in
omit e in
/-- Compatibility projection of the canonical rank for original diagram subtype consumers. -/
theorem functorModelWeakArrows_accessible
    (s : Functor.EssentialIndexData.{w} D C)
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      IsCardinalAccessibleCategory (FunctorModelWeakArrow D C) ν ∧
        (functorModelWeakArrows D C).ι.IsCardinalAccessible ν := by
  obtain ⟨ν, hν, hW⟩ := d.functorWeakEquivalences_accessible s κLP
  let _ : Fact ν.IsRegular := hν
  exact ⟨ν, hν, hW.isCardinalAccessibleCategory, hW.isCardinalAccessible_ι⟩

include d in
omit e in
/-- Compatibility projection used by the original strict weak-arrow solution families. -/
theorem functorModelWeakArrows_isAccessible
    (s : Functor.EssentialIndexData.{w} D C)
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    IsAccessibleCategory.{w} (FunctorModelWeakArrow D C) ∧
      Functor.IsAccessible.{w} (functorModelWeakArrows D C).ι := by
  obtain ⟨ν, hν, hW⟩ := d.functorWeakEquivalences_isAccessible s κLP
  let _ : Fact ν.IsRegular := hν
  let _ : ((weakEquivalences C).functorCategory D).arrowObjectProperty.ι.IsCardinalAccessible ν :=
    hW.isCardinalAccessible_ι
  exact ⟨⟨ν, hν, hW.isCardinalAccessibleCategory⟩,
    Functor.isAccessible_of_isCardinalAccessible _ ν⟩

end HomotopicalAlgebra.CofibrantGenerationData
