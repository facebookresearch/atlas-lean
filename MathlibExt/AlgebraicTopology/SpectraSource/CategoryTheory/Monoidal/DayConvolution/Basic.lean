/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Basic.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.DayConvolution
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor

/-!
# Whiskerings, associators and unitors under a lawful Day convolution structure

For a lawful Day convolution monoidal structure on `D`, Mathlib proves that the faithful functor
`ι : D ⥤ C ⥤ V` carries tensor products of morphisms and associators to their Day convolution
counterparts. This file adds the corresponding statements for left and right whiskerings and for
inverse associators. They are used to transfer the Day convolution braiding to `C ⊛⥤ V`.

For `C ⊛⥤ V` itself, we restate Mathlib's characterisations of the whiskerings, the tensor
product of morphisms, the associator and the unitors along the Day convolution units `η F G` and
`ν C V`, in a form `simp` can use, and prove that morphisms out of `(F ⊗ G) ⊗ H`, `𝟙_ ⊗ F` and
`F ⊗ 𝟙_` are determined by their restrictions along these units.

## Main statements

* `LawfulDayConvolutionMonoidalCategoryStruct.ι_map_whiskerLeft_eq_tensorHom` and
  `LawfulDayConvolutionMonoidalCategoryStruct.ι_map_whiskerRight_eq_tensorHom`: `ι` carries
  whiskerings to Day convolutions with an identity.
* `LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_inv_eq_associator_inv`: `ι`
  carries the inverse associator to the inverse Day convolution associator.
* `DayFunctor.tensor_tensor_hom_ext`, `DayFunctor.unit_tensor_hom_ext`,
  `DayFunctor.tensor_unit_hom_ext`: extensionality for morphisms out of iterated Day convolutions.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct

noncomputable section

namespace LawfulDayConvolutionMonoidalCategoryStruct

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]
  (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]

attribute [local instance] convolution convolution₂ convolution₂'

/-- `ι` carries a left whiskering `d ◁ f` to the Day convolution of `𝟙` and `ι.map f`. -/
lemma ι_map_whiskerLeft_eq_tensorHom (d : D) {d' d'' : D} (f : d' ⟶ d'') :
    (ι C V D).map (d ◁ f) = DayConvolution.map (𝟙 ((ι C V D).obj d)) ((ι C V D).map f) := by
  apply DayConvolution.corepresentableBy ((ι C V D).obj d) ((ι C V D).obj d')
    |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app, DayConvolution.unit_app_map_app,
    NatTrans.id_app, id_tensorHom]
  exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V d f x y

/-- `ι` carries a right whiskering `f ▷ d''` to the Day convolution of `ι.map f` and `𝟙`. -/
lemma ι_map_whiskerRight_eq_tensorHom {d d' : D} (f : d ⟶ d') (d'' : D) :
    (ι C V D).map (f ▷ d'') = DayConvolution.map ((ι C V D).map f) (𝟙 ((ι C V D).obj d'')) := by
  apply DayConvolution.corepresentableBy ((ι C V D).obj d) ((ι C V D).obj d'')
    |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app, DayConvolution.unit_app_map_app,
    NatTrans.id_app, tensorHom_id]
  exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app C V f d'' x y

/-- `ι` carries the inverse associator to the inverse Day convolution associator. -/
lemma ι_map_associator_inv_eq_associator_inv (d d' d'' : D)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)] :
    (ι C V D).map (α_ d d' d'').inv =
      (DayConvolution.associator ((ι C V D).obj d) ((ι C V D).obj d')
        ((ι C V D).obj d'')).inv := by
  rw [← cancel_epi ((ι C V D).map (α_ d d' d'').hom), ← Functor.map_comp, Iso.hom_inv_id,
    Functor.map_id, ι_map_associator_hom_eq_associator_hom, Iso.hom_inv_id]

end LawfulDayConvolutionMonoidalCategoryStruct

namespace DayFunctor

open LawfulDayConvolutionMonoidalCategoryStruct

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-! ### The monoidal structure along the Day convolution units -/

/-- The left whiskering `F ◁ g` restricted along the Day convolution unit `η F G`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_whiskerLeft_natTrans_app (F : C ⊛⥤ V) {G G' : C ⊛⥤ V} (g : G ⟶ G') (x y : C) :
    (η F G).app (x, y) ≫ (F ◁ g).natTrans.app (x ⊗ y) =
      F.functor.obj x ◁ g.natTrans.app y ≫ (η F G').app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V F g x y

/-- The right whiskering `f ▷ G` restricted along the Day convolution unit `η F G`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_whiskerRight_natTrans_app {F F' : C ⊛⥤ V} (f : F ⟶ F') (G : C ⊛⥤ V) (x y : C) :
    (η F G).app (x, y) ≫ (f ▷ G).natTrans.app (x ⊗ y) =
      f.natTrans.app x ▷ G.functor.obj y ≫ (η F' G).app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app C V f G x y

/-- The tensor product `f ⊗ₘ g` restricted along the Day convolution unit `η F G`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_tensorHom_natTrans_app {F F' G G' : C ⊛⥤ V} (f : F ⟶ F') (g : G ⟶ G')
    (x y : C) :
    (η F G).app (x, y) ≫ (f ⊗ₘ g).natTrans.app (x ⊗ y) =
      (f.natTrans.app x ⊗ₘ g.natTrans.app y) ≫ (η F' G').app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_tensorHom_app C V f g x y

/-- The associator `(F ⊗ G) ⊗ H ≅ F ⊗ G ⊗ H` restricted along the Day convolution units: at
`(x, y, z)` it is the associator of `V`, followed by the units and the action of
`F ⊗ G ⊗ H` on the inverse associator of `C`. -/
@[reassoc (attr := simp)]
lemma η_app_whiskerRight_comp_η_app_comp_associator_hom_natTrans_app (F G H : C ⊛⥤ V)
    (x y z : C) :
    (η F G).app (x, y) ▷ H.functor.obj z ≫ (η (F ⊗ G) H).app (x ⊗ y, z) ≫
        (α_ F G H).hom.natTrans.app ((x ⊗ y) ⊗ z) =
      (α_ _ _ _).hom ≫ F.functor.obj x ◁ (η G H).app (y, z) ≫ (η F (G ⊗ H)).app (x, y ⊗ z) ≫
        (F ⊗ G ⊗ H).functor.map (α_ x y z).inv :=
  associator_hom_unit_unit V F G H x y z

/-- The inverse associator restricted along two Day convolution units regroups the three
factors by the inverse pointwise associator. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_η_app_comp_η_app_comp_associator_inv_natTrans_app (F G H : C ⊛⥤ V)
    (x y z : C) :
    F.functor.obj x ◁ (η G H).app (y, z) ≫ (η F (G ⊗ H)).app (x, y ⊗ z) ≫
        (α_ F G H).inv.natTrans.app (x ⊗ y ⊗ z) =
      (α_ _ _ _).inv ≫ (η F G).app (x, y) ▷ H.functor.obj z ≫
        (η (F ⊗ G) H).app (x ⊗ y, z) ≫ ((F ⊗ G) ⊗ H).functor.map (α_ x y z).hom := by
  let : DayConvolution F.functor G.functor := convolution C V (C ⊛⥤ V) F G
  let : DayConvolution G.functor H.functor := convolution C V (C ⊛⥤ V) G H
  let : DayConvolution F.functor (DayConvolution.convolution G.functor H.functor) :=
    convolution₂ C V (C ⊛⥤ V) F G H
  let : DayConvolution (DayConvolution.convolution F.functor G.functor) H.functor :=
    convolution₂' C V (C ⊛⥤ V) F G H
  have h : (α_ F G H).inv.natTrans =
      (DayConvolution.associator F.functor G.functor H.functor).inv :=
    ι_map_associator_inv_eq_associator_inv C V (C ⊛⥤ V) F G H
  rw [h]
  exact DayConvolution.associator_inv_unit_unit F.functor G.functor H.functor x y z

/-- The left unitor `𝟙_ ⊗ F ≅ F` restricted along the Day convolution units. -/
@[reassoc (attr := simp)]
lemma ν_whiskerRight_comp_η_app_comp_leftUnitor_hom_natTrans_app (F : C ⊛⥤ V) (y : C) :
    ν C V ▷ F.functor.obj y ≫ (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
        (λ_ F).hom.natTrans.app (𝟙_ C ⊗ y) =
      (λ_ (F.functor.obj y)).hom ≫ F.functor.map (λ_ y).inv :=
  leftUnitor_hom_unit_app V F y

/-- The right unitor `F ⊗ 𝟙_ ≅ F` restricted along the Day convolution units. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ν_comp_η_app_comp_rightUnitor_hom_natTrans_app (F : C ⊛⥤ V) (x : C) :
    F.functor.obj x ◁ ν C V ≫ (η F (𝟙_ (C ⊛⥤ V))).app (x, 𝟙_ C) ≫
        (ρ_ F).hom.natTrans.app (x ⊗ 𝟙_ C) =
      (ρ_ (F.functor.obj x)).hom ≫ F.functor.map (ρ_ x).inv :=
  rightUnitor_hom_unit_app V F x

/-- Morphisms out of `𝟙_ ⊗ F` are determined by their restrictions along `ν C V` and the Day
convolution unit `η (𝟙_ _) F`. -/
lemma unit_tensor_hom_ext {F G : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⊗ F ⟶ G}
    (h : ∀ y : C, ν C V ▷ F.functor.obj y ≫ (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
        α.natTrans.app (𝟙_ C ⊗ y) =
      ν C V ▷ F.functor.obj y ≫ (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
        β.natTrans.app (𝟙_ C ⊗ y)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _ (η _ F) _
  have : ((𝟙_ (C ⊛⥤ V)).functor ⊠ F.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft _ (νNatTrans C V) F.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft _ (νNatTrans C V)
      F.functor (isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V))).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitLeft _ (νNatTrans C V) F.functor) _
  ext ⟨⟨⟩, y⟩
  simpa using h y

/-- Morphisms out of `F ⊗ 𝟙_` are determined by their restrictions along `ν C V` and the Day
convolution unit `η F (𝟙_ _)`. -/
lemma tensor_unit_hom_ext {F G : C ⊛⥤ V} {α β : F ⊗ 𝟙_ (C ⊛⥤ V) ⟶ G}
    (h : ∀ x : C, F.functor.obj x ◁ ν C V ≫ (η F (𝟙_ (C ⊛⥤ V))).app (x, 𝟙_ C) ≫
        α.natTrans.app (x ⊗ 𝟙_ C) =
      F.functor.obj x ◁ ν C V ≫ (η F (𝟙_ (C ⊛⥤ V))).app (x, 𝟙_ C) ≫
        β.natTrans.app (x ⊗ 𝟙_ C)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _ (η F _) _
  have : (F.functor ⊠ (𝟙_ (C ⊛⥤ V)).functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitRight _ (νNatTrans C V) F.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitRight _ (νNatTrans C V)
      F.functor (isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V))).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitRight _ (νNatTrans C V) F.functor) _
  ext ⟨x, ⟨⟩⟩
  simpa using h x

/-- Morphisms out of `(F ⊗ G) ⊗ H` are determined by their restrictions along the Day
convolution units `η F G` and `η (F ⊗ G) H`. -/
lemma tensor_tensor_hom_ext {F G H K : C ⊛⥤ V} {α β : (F ⊗ G) ⊗ H ⟶ K}
    (h : ∀ x y z : C, (η F G).app (x, y) ▷ H.functor.obj z ≫ (η (F ⊗ G) H).app (x ⊗ y, z) ≫
        α.natTrans.app ((x ⊗ y) ⊗ z) =
      (η F G).app (x, y) ▷ H.functor.obj z ≫ (η (F ⊗ G) H).app (x ⊗ y, z) ≫
        β.natTrans.app ((x ⊗ y) ⊗ z)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _ (η (F ⊗ G) H) _
  have : ((F ⊗ G).functor ⊠ H.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft _ (η F G) H.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft _ (η F G)
      H.functor (isPointwiseLeftKanExtensionConvolutionExtensionUnit F G)).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitLeft _ (η F G) H.functor) _
  ext ⟨⟨x, y⟩, z⟩
  simpa using h x y z

end DayFunctor

end

end CategoryTheory.MonoidalCategory
