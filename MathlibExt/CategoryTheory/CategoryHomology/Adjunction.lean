/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.Basic

/-!
# Category homology and adjunctions

Either functor in an adjunction induces an isomorphism on category homology.
The inverse is induced by the other functor; the unit and counit make the two
composites equal to the corresponding identity maps by natural-transformation
invariance.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u vA uA

namespace CategoryTheory

variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max u v} A] [CategoryWithHomology A]

set_option maxHeartbeats 400000 in
-- The two functor-category composite equalities exceed the default elaboration budget.
/-- Either functor in an adjunction induces an isomorphism on category
homology. -/
noncomputable def categoryHomologyIsoOfAdjunction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (G : D ⥤ C) (h : F ⊣ G)
    (R : A) (n : ℕ) :
    (nerve C).homology R n ≅ (nerve D).homology R n := by
  let H : Cat.{v, u} ⥤ A := categoryHomologyFunctor A R n
  exact
    { hom := H.map F.toCatHom
      inv := H.map G.toCatHom
      hom_inv_id := by
        have hUnit := categoryHomologyMap_eq_of_natTrans A h.unit R n
        calc
          H.map F.toCatHom ≫ H.map G.toCatHom =
              H.map (F.toCatHom ≫ G.toCatHom) :=
            (H.map_comp _ _).symm
          _ = H.map (𝟭 C).toCatHom := hUnit.symm
          _ = 𝟙 _ := by
            change H.map (𝟙 (Cat.of C)) = 𝟙 _
            exact H.map_id (Cat.of C)
      inv_hom_id := by
        have hCounit := categoryHomologyMap_eq_of_natTrans A h.counit R n
        calc
          H.map G.toCatHom ≫ H.map F.toCatHom =
              H.map (G.toCatHom ≫ F.toCatHom) :=
            (H.map_comp _ _).symm
          _ = H.map (𝟭 D).toCatHom := hCounit
          _ = 𝟙 _ := by
            change H.map (𝟙 (Cat.of D)) = 𝟙 _
            exact H.map_id (Cat.of D) }

end CategoryTheory

end
