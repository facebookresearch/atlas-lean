/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Over
public import Mathlib.CategoryTheory.Limits.Comma
public import MathlibExt.CategoryTheory.LiftingProperties.Under

/-!
# The model-category structure on Under categories

For a model category `C` and `S : C`, all three model classes on `Under S`
are created by `Under.forget S`.  This is the literal dual of Mathlib's
construction for `Over S`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] (S : C)

section Cofibrations

variable [CategoryWithCofibrations C]

/-- The Under category creates cofibrations through its forgetful functor. -/
instance underCategoryWithCofibrations : CategoryWithCofibrations (Under S) where
  cofibrations := (cofibrations C).under

lemma cofibrations_under_def :
    cofibrations (Under S) = (cofibrations C).under := rfl

lemma cofibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := by
  simp only [cofibration_iff, cofibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.right := by
  rwa [← cofibrations_under_iff]

private instance cofibrationsUnderRetracts
    [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Under S)).IsStableUnderRetracts := by
  rw [cofibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end Cofibrations

section Fibrations

variable [CategoryWithFibrations C]

/-- The Under category creates fibrations through its forgetful functor. -/
instance underCategoryWithFibrations : CategoryWithFibrations (Under S) where
  fibrations := (fibrations C).under

lemma fibrations_under_def :
    fibrations (Under S) = (fibrations C).under := rfl

lemma fibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := by
  simp only [fibration_iff, fibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Fibration f] : Fibration f.right := by
  rwa [← fibrations_under_iff]

private instance fibrationsUnderRetracts
    [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Under S)).IsStableUnderRetracts := by
  rw [fibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end Fibrations

section WeakEquivalences

variable [CategoryWithWeakEquivalences C]

/-- The Under category creates weak equivalences through its forgetful functor. -/
instance underCategoryWithWeakEquivalences : CategoryWithWeakEquivalences (Under S) where
  weakEquivalences := (weakEquivalences C).under

lemma weakEquivalences_under_def :
    weakEquivalences (Under S) = (weakEquivalences C).under := rfl

lemma weakEquivalences_under_iff {X Y : Under S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := by
  simp only [weakEquivalence_iff, weakEquivalences_under_def,
    MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence f.right := by
  rwa [← weakEquivalences_under_iff]

private instance weakEquivalencesUnderRetracts
    [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Under S)).IsStableUnderRetracts := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

private instance weakEquivalencesUnderTwoOfThree
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Under S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end WeakEquivalences

lemma trivialCofibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Under S) = (trivialCofibrations C).under := rfl

lemma trivialFibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Under S) = (trivialFibrations C).under := rfl

private instance underFactorizations
    (W₁ W₂ : MorphismProperty C) [W₁.HasFactorization W₂] :
    (W₁.under (X := S)).HasFactorization W₂.under where
  nonempty_mapFactorizationData {X Y} f := by
    let hf := W₁.factorizationData W₂ f.right
    let Z : Under S := CategoryTheory.Under.mk (X.hom ≫ hf.i)
    let i : X ⟶ Z := CategoryTheory.Under.homMk (U := X) (V := Z) hf.i (by rfl)
    let p : Z ⟶ Y := CategoryTheory.Under.homMk (U := Z) (V := Y) hf.p (by
      change (X.hom ≫ hf.i) ≫ hf.p = Y.hom
      rw [Category.assoc, hf.fac, CategoryTheory.Under.w f])
    exact ⟨{
      Z := Z
      i := i
      p := p
      hi := hf.hi
      hp := hf.hp
      fac := by
        apply CategoryTheory.Under.UnderMorphism.ext
        exact hf.fac
    }⟩

namespace ModelCategory

/-- The global conditional model structure on `Under S`. -/
instance under [ModelCategory C] : ModelCategory (Under S) where
  cm1a := by
    change HasFiniteLimits (StructuredArrow S (𝟭 C))
    infer_instance
  cm4a _ _ _ _ _ := .under _ _
  cm4b _ _ _ _ _ := .under _ _
  cm5a := by
    rw [fibrations_under_def, trivialCofibrations_under_eq]
    infer_instance
  cm5b := by
    rw [cofibrations_under_def, trivialFibrations_under_eq]
    infer_instance

end ModelCategory

end HomotopicalAlgebra
