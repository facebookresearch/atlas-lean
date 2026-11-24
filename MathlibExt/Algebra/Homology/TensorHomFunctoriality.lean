/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Monoidal

/-!
# Functoriality of `tensorHom`

This module records the composition, identity, and zero laws for `tensorHom`
on homological complexes, together with distributivity of `tensorHom` over
finite sums in each tensor variable.

## Declaration inventory

* `tensorHom_comp_tensorHom`: composition of tensor product maps factors
  through componentwise composition.
* `tensorHom_id_id`: the tensor product of identity maps is the identity.
* `tensorHom_zero` / `zero_tensorHom`: a zero tensor factor gives the zero map.
* `tensorHom_sum`: a fixed first tensor morphism distributes over a finite sum
  in the second variable.
* `sum_tensorHom`: a finite sum in the first tensor variable distributes
  against a fixed second morphism.

## Import justification

`Mathlib.Algebra.Homology.Monoidal` supplies `tensorHom` and the underlying
tensor product of complexes; the direct `Mathlib.Algebra.Homology.Additive`
import supplies the preadditive Hom structure and additive Hom maps used by the
degreewise finite-sum proofs. Both direct imports are used below.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]

variable {I : Type*} [DecidableEq I] [AddMonoid I]
  {c : ComplexShape I} [c.TensorSigns]

theorem tensorHom_comp_tensorHom
    {K₁ L₁ M₁ K₂ L₂ M₂ : HomologicalComplex C c}
    [HasTensor K₁ K₂] [HasTensor L₁ L₂] [HasTensor M₁ M₂]
    (f₁ : K₁ ⟶ L₁) (f₂ : L₁ ⟶ M₁) (g₁ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ =
      tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  apply hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [comp_f, ι_mapBifunctorMap_assoc, ι_mapBifunctorMap]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [NatTrans.comp_app, Category.assoc]
  change
    (f₁.f p ▷ _ ≫ _ ◁ g₁.f q ≫ f₂.f p ▷ _ ≫ _ ◁ g₂.f q ≫ _) =
      (f₁.f p ▷ _ ≫ f₂.f p ▷ _ ≫ _ ◁ g₁.f q ≫ _ ◁ g₂.f q ≫ _)
  rw [MonoidalCategory.whisker_exchange_assoc]

theorem tensorHom_id_id (K L : HomologicalComplex C c) [HasTensor K L] :
    tensorHom (𝟙 K) (𝟙 L) = 𝟙 (tensorObj K L) := by
  apply hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  simp

/-- `tensorHom` with a zero morphism in the second variable is zero. -/
@[simp]
theorem tensorHom_zero
    {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (f : K₁ ⟶ L₁) :
    tensorHom f (0 : K₂ ⟶ L₂) = 0 := by
  apply hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [curriedTensor_obj_obj, ι_mapBifunctorMap, zero_f,
    curriedTensor_map_app, curriedTensor_obj_map, comp_zero]
  change _ ≫ (tensorLeft (L₁.X p)).map (0 : K₂.X q ⟶ L₂.X q) ≫ _ = 0
  rw [Functor.map_zero, zero_comp, comp_zero]

/-- `tensorHom` with a zero morphism in the first variable is zero. -/
@[simp]
theorem zero_tensorHom
    {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (g : K₂ ⟶ L₂) :
    tensorHom (0 : K₁ ⟶ L₁) g = 0 := by
  apply hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [curriedTensor_obj_obj, ι_mapBifunctorMap, zero_f,
    curriedTensor_map_app, curriedTensor_obj_map, comp_zero]
  change (tensorRight (K₂.X q)).map (0 : K₁.X p ⟶ L₁.X p) ≫ _ ≫ _ = 0
  rw [Functor.map_zero, zero_comp]

/-- `tensorHom` distributes a fixed first tensor morphism over a finite sum in
the second variable. -/
theorem tensorHom_sum
    {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (f : K₁ ⟶ L₁) {J : Type*} (s : Finset J)
    (g : J → (K₂ ⟶ L₂)) :
    tensorHom f (∑ j ∈ s, g j) =
      ∑ j ∈ s, tensorHom f (g j) := by
  apply hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  have hsum : (∑ j ∈ s, g j).f q = ∑ j ∈ s, (g j).f q :=
    map_sum (Hom.fAddMonoidHom q) _ _
  have hsum' :
      (∑ j ∈ s, tensorHom f (g j)).f n =
        ∑ j ∈ s, (tensorHom f (g j)).f n :=
    map_sum (Hom.fAddMonoidHom n) _ _
  have hmap : ((curriedTensor C).obj (L₁.X p)).map (∑ j ∈ s, (g j).f q) =
      ∑ j ∈ s, ((curriedTensor C).obj (L₁.X p)).map ((g j).f q) :=
    map_sum (((curriedTensor C).obj (L₁.X p)).mapAddHom) _ _
  rw [ι_mapBifunctorMap, hsum, hmap, hsum']
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [ι_mapBifunctorMap]

/-- `tensorHom` distributes a finite sum in the first tensor variable against a
fixed second morphism. -/
theorem sum_tensorHom
    {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    {J : Type*} (s : Finset J)
    (f : J → (K₁ ⟶ L₁)) (g : K₂ ⟶ L₂) :
    tensorHom (∑ j ∈ s, f j) g =
      ∑ j ∈ s, tensorHom (f j) g := by
  apply hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  have hsum : (∑ j ∈ s, f j).f p = ∑ j ∈ s, (f j).f p :=
    map_sum (Hom.fAddMonoidHom p) _ _
  have hsum' :
      (∑ j ∈ s, tensorHom (f j) g).f n =
        ∑ j ∈ s, (tensorHom (f j) g).f n :=
    map_sum (Hom.fAddMonoidHom n) _ _
  have hmap : (curriedTensor C).map (∑ j ∈ s, (f j).f p) =
      ∑ j ∈ s, (curriedTensor C).map ((f j).f p) :=
    map_sum ((curriedTensor C).mapAddHom) _ _
  have happ : ((∑ j ∈ s, (curriedTensor C).map ((f j).f p)).app (K₂.X q)) =
      ∑ j ∈ s, (((curriedTensor C).map ((f j).f p)).app (K₂.X q)) :=
    NatTrans.app_sum s (K₂.X q) fun i => (curriedTensor C).map ((f i).f p)
  rw [ι_mapBifunctorMap, hsum, hmap, happ, hsum']
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [ι_mapBifunctorMap]

end HomologicalComplex
