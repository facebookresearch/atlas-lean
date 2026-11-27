/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# Homology of small categories

The homology of a small category is the simplicial homology of its nerve.
A functor induces the corresponding nerve map on homology, and naturally
related functors induce the same map. This construction is functorial in the
small category.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (A : Type u₂) [Category.{v₂} A] [Preadditive A]
  [HasCoproducts.{max u₁ v₁} A] [CategoryWithHomology A]

/-- Homology in degree `n` of the nerve of a small category, functorial in the category. -/
noncomputable def categoryHomologyFunctor (R : A) (n : ℕ) :
    CategoryTheory.Functor Cat.{v₁, u₁} A :=
  nerveFunctor.{v₁, u₁} ⋙ SSet.homologyFunctor R n

/-- The degree-n category-homology functor assigns degree-n simplicial homology of the nerve with
the chosen coefficient object. -/
@[simp]
theorem categoryHomologyFunctor_obj (R : A) (n : ℕ)
    (C : Cat.{v₁, u₁}) :
    (categoryHomologyFunctor A R n).obj C =
      (nerve C).homology R n := rfl

/-- A functor of small categories induces the homology map of its nerve map with the chosen
coefficient object. -/
@[simp]
theorem categoryHomologyFunctor_map (R : A) (n : ℕ)
    {C D : Cat.{v₁, u₁}} (F : C ⟶ D) :
    (categoryHomologyFunctor A R n).map F =
      SSet.homologyMap (nerveMap F.toFunctor) R n := rfl

/-- Naturally transformed functors induce the same map on category homology. -/
theorem categoryHomologyMap_eq_of_natTrans
    {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    {F G : CategoryTheory.Functor C D} (α : F ⟶ G)
    (R : A) (n : ℕ) :
    (categoryHomologyFunctor A R n).map F.toCatHom =
      (categoryHomologyFunctor A R n).map G.toCatHom := by
  change SSet.homologyMap (nerveMap F) R n =
    SSet.homologyMap (nerveMap G) R n
  exact (NatTrans.nerveHomotopy α).congr_homologyMap R n

/-- Naturally isomorphic functors induce the same map on category homology. -/
theorem categoryHomologyMap_eq_of_natIso
    {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    {F G : CategoryTheory.Functor C D} (e : F ≅ G)
    (R : A) (n : ℕ) :
    (categoryHomologyFunctor A R n).map F.toCatHom =
      (categoryHomologyFunctor A R n).map G.toCatHom :=
  categoryHomologyMap_eq_of_natTrans A e.hom R n

/-- An equivalence of categories induces an isomorphism on category homology. -/
noncomputable def categoryHomologyIsoOfEquivalence
    {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    (e : C ≌ D) (R : A) (n : ℕ) :
    (nerve C).homology R n ≅ (nerve D).homology R n := by
  let H : Cat.{v₁, u₁} ⥤ A := categoryHomologyFunctor A R n
  let eH : H.obj (Cat.of C) ≅ H.obj (Cat.of D) :=
    { hom := H.map e.functor.toCatHom
      inv := H.map e.inverse.toCatHom
      hom_inv_id := by
        have h := categoryHomologyMap_eq_of_natIso A e.unitIso R n
        calc
          H.map e.functor.toCatHom ≫ H.map e.inverse.toCatHom =
              H.map (e.functor.toCatHom ≫ e.inverse.toCatHom) :=
            (H.map_comp _ _).symm
          _ = H.map (𝟭 C).toCatHom := h.symm
          _ = 𝟙 _ := by
            change H.map (𝟙 (Cat.of C)) = 𝟙 _
            exact H.map_id (Cat.of C)
      inv_hom_id := by
        have h := categoryHomologyMap_eq_of_natIso A e.counitIso R n
        calc
          H.map e.inverse.toCatHom ≫ H.map e.functor.toCatHom =
              H.map (e.inverse.toCatHom ≫ e.functor.toCatHom) :=
            (H.map_comp _ _).symm
          _ = H.map (𝟭 D).toCatHom := h
          _ = 𝟙 _ := by
            change H.map (𝟙 (Cat.of D)) = 𝟙 _
            exact H.map_id (Cat.of D) }
  exact eH

end CategoryTheory

end
