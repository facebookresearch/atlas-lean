/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Monoidal
public import MathlibExt.CategoryTheory.DGSource.CochainTensorSummands

/-!
# Functoriality and additivity of tensor maps of complexes

Let C be preadditive and monoidal with tensor product additive in both variables, and let c be a
complex shape on an additive monoid with tensor signs. When the relevant tensor complexes exist,
tensoring complex maps preserves identities and componentwise composition, vanishes if either
factor is zero, and distributes over finite sums in either factor.
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

attribute [simp] tensorHom_zero zero_tensorHom

/-- Let C be a preadditive monoidal category with tensor product additive in each variable, I an
additive monoid with decidable equality, and c a complex shape on I equipped with tensor signs.
Let f : K₁ → L₁ and g_j : K₂ → L₂ be complex maps, with source and target tensor complexes
defined, and let s be a finite subset of an arbitrary index type J. Then tensorHom(f,∑_{j∈s}g_j)
= ∑_{j∈s}tensorHom(f,g_j). -/
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

/-- Let C be a preadditive monoidal category with tensor product additive in each variable, I an
additive monoid with decidable equality, and c a complex shape on I equipped with tensor signs.
Let f_j : K₁ → L₁ and g : K₂ → L₂ be complex maps, with source and target tensor complexes
defined, and s a finite subset of an arbitrary index type J. Then tensorHom(∑_{j∈s}f_j,g) =
∑_{j∈s}tensorHom(f_j,g). -/
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
