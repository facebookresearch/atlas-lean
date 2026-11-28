/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.TensorHomotopy

/-!
# Naturality of a tensor homotopy

For homotopies from projectors p_K,p_L to identities and corresponding target homotopies,
assume componentwise naturality with maps a,b and the second-projector square p_L b = b p_L′.
The combined tensor homotopy commutes in every component with a⊗b.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]

/-- The tensor homotopy components commute with compatible maps.

Under the supplied component homotopy squares and second-projector compatibility,
h_tensor(i,j) followed by (a⊗b)_j equals (a⊗b)_i followed by the target tensor homotopy. -/
theorem tensorHomotopy_hom_naturality
    {K K' L L' : ChainComplex C ℕ}
    {pK : K ⟶ K} {pK' : K' ⟶ K'}
    {pL : L ⟶ L} {pL' : L' ⟶ L'}
    [HasTensor K L] [HasTensor K' L']
    (hK : Homotopy pK (𝟙 K)) (hK' : Homotopy pK' (𝟙 K'))
    (hL : Homotopy pL (𝟙 L)) (hL' : Homotopy pL' (𝟙 L'))
    (a : K ⟶ K') (b : L ⟶ L')
    (hpL : pL ≫ b = b ≫ pL')
    (hKNat : ∀ i j, hK.hom i j ≫ a.f j = a.f i ≫ hK'.hom i j)
    (hLNat : ∀ i j, hL.hom i j ≫ b.f j = b.f i ≫ hL'.hom i j)
    (i j : ℕ) :
    (tensorHomotopy hK hL).hom i j ≫ (tensorHom a b).f j =
      (tensorHom a b).f i ≫ (tensorHomotopy hK' hL').hom i j := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [curriedTensor_obj_obj, tensorHomotopy, Homotopy.trans_hom,
    Preadditive.add_comp, Preadditive.comp_add, ι_mapBifunctorMap_assoc,
    curriedTensor_map_app, curriedTensor_obj_map]
  congr 1
  · dsimp only [mapBifunctorMapHomotopy₁]
    erw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₁_assoc
      hK pL (curriedTensor C) (ComplexShape.down ℕ)
      ((ComplexShape.down ℕ).prev p) p q i j hpq rfl]
    erw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
      hK' pL' (curriedTensor C) (ComplexShape.down ℕ)
      ((ComplexShape.down ℕ).prev p) p q i j hpq rfl]
    by_cases hpj : (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev p, q) = j
    · simp only [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hpj,
        curriedTensor_obj_obj, ChainComplex.prev, ComplexShape.ε₁_def,
        curriedTensor_map_app, curriedTensor_obj_map, one_smul, Category.assoc]
      slice_lhs 3 4 => rw [ι_mapBifunctorMap]
      have hpLq := congrArg (fun k => k.f q) hpL
      simp only [comp_f] at hpLq
      slice_lhs 2 3 => erw [MonoidalCategory.whisker_exchange]
      slice_lhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight]
      slice_lhs 1 1 => rw [hKNat]
      rw [MonoidalCategory.comp_whiskerRight_assoc]
      slice_lhs 3 4 => erw [← MonoidalCategory.whiskerLeft_comp]
      slice_lhs 3 3 => rw [hpLq]
      rw [MonoidalCategory.whiskerLeft_comp_assoc]
      slice_lhs 2 3 => rw [← MonoidalCategory.whisker_exchange]
      simp only [Category.assoc]
    · simp only [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hpj,
        comp_zero, smul_zero, zero_comp]
  · dsimp only [mapBifunctorMapHomotopy₂]
    erw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₂_assoc
      (𝟙 K) hL (curriedTensor C) (ComplexShape.down ℕ)
      p ((ComplexShape.down ℕ).prev q) q i j hpq rfl]
    erw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
      (𝟙 K') hL' (curriedTensor C) (ComplexShape.down ℕ)
      p ((ComplexShape.down ℕ).prev q) q i j hpq rfl]
    by_cases hqj : (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) = j
    · simp only [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hqj,
        curriedTensor_obj_obj, ChainComplex.prev, ComplexShape.ε₂_def,
        ComplexShape.ε_down_ℕ, id_f,
        curriedTensor_obj_map, Linear.units_smul_comp,
        Category.assoc, Linear.comp_units_smul, smul_left_cancel_iff]
      slice_lhs 3 4 => rw [ι_mapBifunctorMap]
      simp only [curriedTensor_map_app, MonoidalCategory.id_whiskerRight,
        Category.id_comp]
      slice_lhs 1 2 => erw [MonoidalCategory.whisker_exchange]
      slice_lhs 2 3 => erw [← MonoidalCategory.whiskerLeft_comp]
      slice_lhs 2 2 => rw [hLNat]
      rw [MonoidalCategory.whiskerLeft_comp_assoc]
    · simp only [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hqj,
        comp_zero, smul_zero, zero_comp]

end HomologicalComplex
