/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntMapIso

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
variable (T : SymmetricTrace C) (S : SymmetricTrace D) (F G : C ⥤ D) [F.Braided] [G.Braided]
  (hF : T.Preserves S F) (hG : T.Preserves S G) (i : F ≅ G) [NatTrans.IsMonoidal i.hom]
example : IntConstruction.map T S F hF ≅ IntConstruction.map T S G hG :=
  IntConstruction.mapIso T S hF hG i


open IntConstruction Functor.LaxMonoidal Functor.OplaxMonoidal

-- Neither category is assumed rigid, and the supplied isomorphism need not be identity.
example : NatTrans.IsMonoidal (mapIso T S hF hG i).hom := inferInstance
example : NatTrans.IsMonoidal (mapIso T S hF hG i).inv := inferInstance
example (X : IntConstruction T) :
    hom S ((mapIso T S hF hG i).hom.app X) =
      i.hom.app X.positive ⊗ₘ i.inv.app X.negative := hom_mapIso_hom_app T S hF hG i X
example (A U : C) :
    hom S ((mapIso T S hF hG i).inv.app (⟨A, U⟩ : IntConstruction T)) =
      i.inv.app A ⊗ₘ i.hom.app U := hom_mapIso_inv_app T S hF hG i _

-- Arbitrary crossed maps, not merely separated maps, satisfy naturality.
example {X Y : IntConstruction T} (f : X ⟶ Y) :
    (map T S F hF).map f ≫ (mapIso T S hF hG i).hom.app Y =
      (mapIso T S hF hG i).hom.app X ≫ (map T S G hG).map f :=
  (mapIso T S hF hG i).hom.naturality f
example {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    mapCrossed F f ≫ (i.hom.app B ⊗ₘ i.hom.app U) =
      (i.hom.app A ⊗ₘ i.hom.app V) ≫ mapCrossed G f := mapCrossed_naturality i f
example {X Y : IntConstruction T} (f : X ⟶ Y) :
    (mapIso T S hF hG i).inv.app X ≫ (map T S F hF).map f ≫
      (mapIso T S hF hG i).hom.app Y = (map T S G hG).map f :=
  NatIso.naturality_1 (mapIso T S hF hG i) f

example (X : IntConstruction T) :
    (mapIso T S hF hG i).hom.app X ≫ (mapIso T S hF hG i).inv.app X =
      𝟙 ((map T S F hF).obj X) := Iso.hom_inv_id_app _ _
example (X : IntConstruction T) :
    (mapIso T S hF hG i).inv.app X ≫ (mapIso T S hF hG i).hom.app X =
      𝟙 ((map T S G hG).obj X) := Iso.inv_hom_id_app _ _
example : ε (map T S F hF) ≫ (mapIso T S hF hG i).hom.app (𝟙_ (IntConstruction T)) =
    ε (map T S G hG) := NatTrans.IsMonoidal.unit
example (X Y : IntConstruction T) :
    μ (map T S F hF) X Y ≫ (mapIso T S hF hG i).hom.app (X ⊗ Y) =
      ((mapIso T S hF hG i).hom.app X ⊗ₘ (mapIso T S hF hG i).hom.app Y) ≫
        μ (map T S G hG) X Y := NatTrans.IsMonoidal.tensor X Y

-- Projection bridges expose the standard identity/inverse transformation instances.
local instance : NatTrans.IsMonoidal (Iso.refl F).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (𝟙 F))
local instance : NatTrans.IsMonoidal i.symm.hom :=
  inferInstanceAs (NatTrans.IsMonoidal i.inv)

example : mapIso T S hF hF (Iso.refl F) = Iso.refl (map T S F hF) := mapIso_refl T S hF
example : mapIso T S hG hF i.symm = (mapIso T S hF hG i).symm := mapIso_symm T S hF hG i

section Composition
variable (H : C ⥤ D) [H.Braided] (hH : T.Preserves S H)
variable (j : G ≅ H) [NatTrans.IsMonoidal j.hom]
local instance : NatTrans.IsMonoidal (i ≪≫ j).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (i.hom ≫ j.hom))

example : mapIso T S hF hH (i ≪≫ j) =
    mapIso T S hF hG i ≪≫ mapIso T S hG hH j := mapIso_trans T S hF hG i hH j
example (X : IntConstruction T) :
    hom S ((mapIso T S hF hH (i ≪≫ j)).hom.app X) =
      (i.hom.app X.positive ≫ j.hom.app X.positive) ⊗ₘ
        (j.inv.app X.negative ≫ i.inv.app X.negative) := rfl
end Composition

-- Unit source objects still retain the negative inverse component.
example : hom S ((mapIso T S hF hG i).hom.app (𝟙_ (IntConstruction T))) =
    i.hom.app (𝟙_ C) ⊗ₘ i.inv.app (𝟙_ C) := rfl

-- A canonical monoidal isomorphism can be lifted without any source duals.
local instance : NatTrans.IsMonoidal F.rightUnitor.hom := inferInstance
example : map T S (F ⋙ 𝟭 D) (hF.comp S.preserves_id) ≅ map T S F hF :=
  mapIso T S (hF.comp S.preserves_id) hF F.rightUnitor
