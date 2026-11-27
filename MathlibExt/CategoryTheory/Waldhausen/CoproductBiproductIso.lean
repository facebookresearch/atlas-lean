/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductFunctor
public import MathlibExt.CategoryTheory.Limits.Shapes.BiproductFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Chosen Waldhausen coproducts and biproducts

Let C be preadditive with zero, binary biproducts and a Waldhausen structure without the gluing
axiom. The chosen zero-pushout coproduct cofan and the biproduct cofan represent the same pair
diagram.

Their canonical colimit isomorphism X⊔wY≅X⊞Y preserves both injections and is natural in pair
maps. These charts assemble into a natural isomorphism of the chosen coproduct and biproduct
functors. Object and Hom universes u,v are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [WaldhausenCategoryWithoutGluing C]

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. The two binary cofans are colimiting on the same pair, giving this
unique isomorphism that preserves their injections. -/
def binaryCoproductBiproductIso (X Y : C) :
    (binaryCoproductColimitCocone C (pair X Y)).cocone.pt ≅ X ⊞ Y :=
  (binaryCoproductColimitCocone C (pair X Y)).isColimit.coconePointUniqueUpToIso
    (BinaryBiproduct.isColimit X Y)

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. The first chosen coproduct injection followed by c is the first
biproduct injection. -/
theorem binaryCoproductBiproductIso_inl_hom (X Y : C) :
    (binaryCoproductColimitCocone C (pair X Y)).cocone.ι.app ⟨WalkingPair.left⟩ ≫
      (binaryCoproductBiproductIso C X Y).hom = biprod.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
    (BinaryBiproduct.isColimit X Y) ⟨WalkingPair.left⟩

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. The second chosen coproduct injection followed by c is the second
biproduct injection. -/
theorem binaryCoproductBiproductIso_inr_hom (X Y : C) :
    (binaryCoproductColimitCocone C (pair X Y)).cocone.ι.app ⟨WalkingPair.right⟩ ≫
      (binaryCoproductBiproductIso C X Y).hom = biprod.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
    (BinaryBiproduct.isColimit X Y) ⟨WalkingPair.right⟩

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. The first biproduct injection followed by c⁻¹ is the first chosen
coproduct injection. -/
theorem binaryCoproductBiproductIso_inl_inv (X Y : C) :
    biprod.inl ≫ (binaryCoproductBiproductIso C X Y).inv =
      (binaryCoproductColimitCocone C (pair X Y)).cocone.ι.app ⟨WalkingPair.left⟩ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
    (BinaryBiproduct.isColimit X Y) ⟨WalkingPair.left⟩

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. The second biproduct injection followed by c⁻¹ is the second chosen
coproduct injection. -/
theorem binaryCoproductBiproductIso_inr_inv (X Y : C) :
    biprod.inr ≫ (binaryCoproductBiproductIso C X Y).inv =
      (binaryCoproductColimitCocone C (pair X Y)).cocone.ι.app ⟨WalkingPair.right⟩ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (binaryCoproductColimitCocone C (pair X Y)).isColimit
    (BinaryBiproduct.isColimit X Y) ⟨WalkingPair.right⟩

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. For f:X→X′ and g:Y→Y′, the chosen coproduct map followed by c_(X′,Y′)
equals c_(X,Y) followed by the biproduct map of f,g. -/
theorem binaryCoproductBiproductIso_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    binaryCoproductMap C f g ≫ (binaryCoproductBiproductIso C X' Y').hom =
      (binaryCoproductBiproductIso C X Y).hom ≫ biprod.map f g := by
  let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone
  let c' : BinaryCofan X' Y' := (binaryCoproductColimitCocone C (pair X' Y')).cocone
  have hL : c.inl ≫ binaryCoproductMap C f g = f ≫ c'.inl := binaryCoproductMap_inl C f g
  have hR : c.inr ≫ binaryCoproductMap C f g = g ≫ c'.inr := binaryCoproductMap_inr C f g
  have hL₀ : c.inl ≫ (binaryCoproductBiproductIso C X Y).hom = biprod.inl :=
    binaryCoproductBiproductIso_inl_hom C X Y
  have hR₀ : c.inr ≫ (binaryCoproductBiproductIso C X Y).hom = biprod.inr :=
    binaryCoproductBiproductIso_inr_hom C X Y
  have hL₁ : c'.inl ≫ (binaryCoproductBiproductIso C X' Y').hom = biprod.inl :=
    binaryCoproductBiproductIso_inl_hom C X' Y'
  have hR₁ : c'.inr ≫ (binaryCoproductBiproductIso C X' Y').hom = biprod.inr :=
    binaryCoproductBiproductIso_inr_hom C X' Y'
  apply BinaryCofan.IsColimit.hom_ext (binaryCoproductColimitCocone C (pair X Y)).isColimit
  · calc
      _ = (c.inl ≫ binaryCoproductMap C f g) ≫ (binaryCoproductBiproductIso C X' Y').hom :=
        (Category.assoc _ _ _).symm
      _ = (f ≫ c'.inl) ≫ (binaryCoproductBiproductIso C X' Y').hom :=
        congrArg (fun t => t ≫ (binaryCoproductBiproductIso C X' Y').hom) hL
      _ = f ≫ (c'.inl ≫ (binaryCoproductBiproductIso C X' Y').hom) := Category.assoc _ _ _
      _ = f ≫ biprod.inl := congrArg (fun t => f ≫ t) hL₁
      _ = biprod.inl ≫ biprod.map f g := (biprod.inl_map f g).symm
      _ = (c.inl ≫ (binaryCoproductBiproductIso C X Y).hom) ≫ biprod.map f g :=
        congrArg (fun t => t ≫ biprod.map f g) hL₀.symm
      _ = _ := Category.assoc _ _ _
  · calc
      _ = (c.inr ≫ binaryCoproductMap C f g) ≫ (binaryCoproductBiproductIso C X' Y').hom :=
        (Category.assoc _ _ _).symm
      _ = (g ≫ c'.inr) ≫ (binaryCoproductBiproductIso C X' Y').hom :=
        congrArg (fun t => t ≫ (binaryCoproductBiproductIso C X' Y').hom) hR
      _ = g ≫ (c'.inr ≫ (binaryCoproductBiproductIso C X' Y').hom) := Category.assoc _ _ _
      _ = g ≫ biprod.inr := congrArg (fun t => g ≫ t) hR₁
      _ = biprod.inr ≫ biprod.map f g := (biprod.inr_map f g).symm
      _ = (c.inr ≫ (binaryCoproductBiproductIso C X Y).hom) ≫ biprod.map f g :=
        congrArg (fun t => t ≫ biprod.map f g) hR₀.symm
      _ = _ := Category.assoc _ _ _

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. These charts give a natural isomorphism from the chosen Waldhausen
binary coproduct functor C×C→C to the biproduct functor. -/
def coproductBiproductNatIso : waldhausenCoproductFunctor C ≅ biprodFunctor C :=
  NatIso.ofComponents
    (fun p => eqToIso (waldhausenCoproductFunctor_obj C p) ≪≫
      binaryCoproductBiproductIso C p.1 p.2)
    (fun {p q} a => by
      change (waldhausenCoproductFunctor C).map a ≫
          (eqToHom (waldhausenCoproductFunctor_obj C q) ≫
            (binaryCoproductBiproductIso C q.1 q.2).hom) =
        (eqToHom (waldhausenCoproductFunctor_obj C p) ≫
          (binaryCoproductBiproductIso C p.1 p.2).hom) ≫ biprod.map a.1 a.2
      rw [waldhausenCoproductFunctor_map]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [binaryCoproductBiproductIso_naturality])

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. At (X,Y), the forward natural component is the chosen
coproduct-to-biproduct chart, after identifying the functor value with its selected coproduct
apex. -/
theorem coproductBiproductNatIso_hom_app (X Y : C) :
    (coproductBiproductNatIso C).hom.app (X, Y) =
      eqToHom (waldhausenCoproductFunctor_obj C (X, Y)) ≫
        (binaryCoproductBiproductIso C X Y).hom := rfl

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. At (X,Y), the inverse natural component is the inverse colimit chart,
with the chosen coproduct apex identified with its functor value. -/
theorem coproductBiproductNatIso_inv_app (X Y : C) :
    (coproductBiproductNatIso C).inv.app (X, Y) =
      (binaryCoproductBiproductIso C X Y).inv ≫
        eqToHom (waldhausenCoproductFunctor_obj C (X, Y)).symm := rfl

/-- Let C be preadditive with a zero object, binary biproducts and a Waldhausen structure without
the gluing axiom. For X,Y∈C, let X⊔wY be its chosen zero-pushout coproduct and c:X⊔wY≅X⊞Y the
canonical colimit chart. The forward natural components commute with the whole pair map (f,g),
using the chosen coproduct map on the source and the biproduct map on the target. -/
theorem coproductBiproductNatIso_hom_naturality {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (waldhausenCoproductFunctor C).map (show (X, Y) ⟶ (X', Y') from (f, g)) ≫
        (coproductBiproductNatIso C).hom.app (X', Y') =
      (coproductBiproductNatIso C).hom.app (X, Y) ≫ biprod.map f g :=
  (coproductBiproductNatIso C).hom.naturality (show (X, Y) ⟶ (X', Y') from (f, g))

end CategoryTheory.Waldhausen

end
