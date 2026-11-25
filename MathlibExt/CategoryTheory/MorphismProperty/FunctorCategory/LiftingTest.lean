/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.LiftingTest
public import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence

/-!
# Original diagram lifting tests over a genuine small index presentation

A fixed tagged collection retains every component test and both original
Arrow map functions. Its working-size normalization is explicit. A genuine
index equivalence then makes the collected test detect every original
component, including original presentations whose object set is larger
than the working universe.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w t uA vA uS uD vD vS uC vC s

open CategoryTheory TypeCat

namespace CategoryTheory.MorphismProperty.LiftingTest

section Collection

variable {A : Type uA} [Category.{vA} A] {S : Type uS}
  (T : S → A ⥤ Arrow (Type t))

/-- The entire original tagged family of source elements of a fixed test collection. -/
abbrev CollectionLeft (p : A) : Type (max uS t) :=
  Σ x : S, ((T x).obj p).left

/-- The entire original tagged family of target elements of that same collection. -/
abbrev CollectionRight (p : A) : Type (max uS t) :=
  Σ x : S, ((T x).obj p).right

/-- The fixed collection retains the same original tag and the actual component test. -/
def collectionFunction (p : A) : CollectionLeft T p → CollectionRight T p :=
  fun z => ⟨z.1, ((T z.1).obj p).hom z.2⟩

/-- The full source map applies the actual component Arrow map without changing its tag. -/
def collectionLeftMap {p q : A} (τ : p ⟶ q) :
    CollectionLeft T p → CollectionLeft T q :=
  fun z => ⟨z.1, ((T z.1).map τ).left z.2⟩

/-- The full target map applies the actual component Arrow map without changing its tag. -/
def collectionRightMap {p q : A} (τ : p ⟶ q) :
    CollectionRight T p → CollectionRight T q :=
  fun z => ⟨z.1, ((T z.1).map τ).right z.2⟩

/-- A fixed tagged family of actual test functors gives its literal tagged test functor. -/
def collectionFunctor : A ⥤ Arrow (Type (max uS t)) where
  obj p := Arrow.mk (ofHom (collectionFunction T p))
  map {p q} τ := Arrow.homMk (ofHom (collectionLeftMap T τ))
    (ofHom (collectionRightMap T τ)) (by
      apply ConcreteCategory.hom_ext
      intro z
      apply congrArg (fun a => (⟨z.1, a⟩ : CollectionRight T q))
      exact ConcreteCategory.congr_hom ((T z.1).map τ).w z.2)
  map_id p := by
    apply Arrow.hom_ext
    · apply ConcreteCategory.hom_ext
      intro z
      change (⟨z.1, ((T z.1).map (𝟙 p)).left z.2⟩ : CollectionLeft T p) = z
      rw [(T z.1).map_id]
      cases z
      rfl
    · apply ConcreteCategory.hom_ext
      intro z
      change (⟨z.1, ((T z.1).map (𝟙 p)).right z.2⟩ : CollectionRight T p) = z
      rw [(T z.1).map_id]
      cases z
      rfl
  map_comp {p q r} τ σ := by
    apply Arrow.hom_ext
    · apply ConcreteCategory.hom_ext
      intro z
      change (⟨z.1, ((T z.1).map (τ ≫ σ)).left z.2⟩ : CollectionLeft T r) =
        ⟨z.1, ((T z.1).map σ).left (((T z.1).map τ).left z.2)⟩
      rw [(T z.1).map_comp]
      rfl
    · apply ConcreteCategory.hom_ext
      intro z
      change (⟨z.1, ((T z.1).map (τ ≫ σ)).right z.2⟩ : CollectionRight T r) =
        ⟨z.1, ((T z.1).map σ).right (((T z.1).map τ).right z.2)⟩
      rw [(T z.1).map_comp]
      rfl

/-- The whole collected object function is the original tagged family of component tests. -/
theorem collectionFunctor_hom_function (p : A) :
    ((collectionFunctor T).obj p).hom = ofHom (collectionFunction T p) := rfl

/-- The entire collected source map is the original tagged family of component source maps. -/
theorem collectionFunctor_map_left_function {p q : A} (τ : p ⟶ q) :
    ((collectionFunctor T).map τ).left = ofHom (collectionLeftMap T τ) := rfl

/-- The entire collected target map is the original tagged family of component target maps. -/
theorem collectionFunctor_map_right_function {p q : A} (τ : p ⟶ q) :
    ((collectionFunctor T).map τ).right = ofHom (collectionRightMap T τ) := rfl

/-- Surjectivity of the actual tagged function is exactly surjectivity of every component. -/
theorem collectionFunctor_surjective_iff (p : A) :
    Function.Surjective ((collectionFunctor T).obj p).hom ↔
      ∀ x : S, Function.Surjective ((T x).obj p).hom := by
  change Function.Surjective (collectionFunction T p) ↔ _
  constructor
  · intro h x z
    obtain ⟨⟨x', l⟩, hl⟩ := h ⟨x, z⟩
    have htag : x' = x := congrArg Sigma.fst hl
    subst x'
    change (⟨x, ((T x).obj p).hom l⟩ : CollectionRight T p) = ⟨x, z⟩ at hl
    exact ⟨l, eq_of_heq (Sigma.mk.inj_iff.mp hl).2⟩
  · intro h z
    rcases z with ⟨x, z⟩
    obtain ⟨l, hl⟩ := h x z
    exact ⟨⟨x, l⟩, congrArg (fun a => (⟨x, a⟩ : CollectionRight T p)) hl⟩

end Collection

section OriginalDiagrams

variable {D : Type uD} [Category.{vD} D]
  {S : Type uS} [Category.{vS} S] {C : Type uC} [Category.{vC} C]
  {ι : Type s} [Small.{w} S] [Small.{w} ι] [LocallySmall.{w} C]
  (e : D ≌ S) (f : ι → Arrow C)

/-- Each representative tests its actual original component with the same base test. -/
def componentFunctor (x : S) : Arrow (D ⥤ C) ⥤ Arrow (Type w) :=
  Functor.mapArrow ((evaluation D C).obj (e.inverse.obj x)) ⋙ smallFunctor f

/-- The actual component collection retains every original representative and base test tag. -/
def diagramCollection : Arrow (D ⥤ C) ⥤ Arrow (Type (max uS w)) :=
  collectionFunctor (componentFunctor e f)

/-- The actual collected source is working-small over the given representative indices. -/
instance diagramCollection_left_small (p : Arrow (D ⥤ C)) :
    Small.{w} ((diagramCollection e f).obj p).left := by
  change Small.{w} (Σ x : S, ((componentFunctor e f x).obj p).left)
  infer_instance

/-- The actual collected target is working-small with every original tag retained. -/
instance diagramCollection_right_small (p : Arrow (D ⥤ C)) :
    Small.{w} ((diagramCollection e f).obj p).right := by
  change Small.{w} (Σ x : S, ((componentFunctor e f x).obj p).right)
  infer_instance

/-- The working-size diagram test starts from the original diagram Arrow category. -/
def diagramFunctor : Arrow (D ⥤ C) ⥤ Arrow (Type w) := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((diagramCollection e f).obj p).left :=
    diagramCollection_left_small e f
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((diagramCollection e f).obj p).right :=
    diagramCollection_right_small e f
  exact normalizedFunctor (diagramCollection e f)

/-- The collected representative test is surjective exactly at every original component. -/
theorem diagramFunctor_surjective_iff (p : Arrow (D ⥤ C)) :
    Function.Surjective ((diagramFunctor e f).obj p).hom ↔
      ((MorphismProperty.ofHoms (fun k => (f k).hom)).rlp).functorCategory D p.hom := by
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((diagramCollection e f).obj p).left :=
    diagramCollection_left_small e f
  let _ : ∀ p : Arrow (D ⥤ C), Small.{w} ((diagramCollection e f).obj p).right :=
    diagramCollection_right_small e f
  rw [show diagramFunctor e f = normalizedFunctor (diagramCollection e f) from rfl,
    normalizedFunctor_surjective_iff]
  rw [show diagramCollection e f = collectionFunctor (componentFunctor e f) from rfl,
    collectionFunctor_surjective_iff]
  let P : MorphismProperty C := (MorphismProperty.ofHoms (fun k => (f k).hom)).rlp
  let _ : P.RespectsIso := by
    apply MorphismProperty.respectsIso_of_isStableUnderComposition
    intro X Y i hi
    let _ : IsIso i := hi
    exact (MorphismProperty.ofHoms (fun k => (f k).hom)).rlp_of_isIso i
  rw [← functorCategory_inverseImage_congrLeft e P]
  change (∀ x : S, Function.Surjective
    ((smallFunctor f).obj (Arrow.mk (p.hom.app (e.inverse.obj x)))).hom) ↔
      ∀ x : S, P (p.hom.app (e.inverse.obj x))
  apply forall_congr'
  intro x
  exact smallFunctor_surjective_iff f (Arrow.mk (p.hom.app (e.inverse.obj x)))

end OriginalDiagrams
end CategoryTheory.MorphismProperty.LiftingTest
