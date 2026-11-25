/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Braided.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Basic

/-!
# The braided and symmetric Day convolution monoidal structures on `C ⊛⥤ V`

For braided monoidal categories `C` and `V`, Mathlib constructs the Day convolution braiding
`DayConvolution.braiding F G : F ⊛ G ≅ G ⊛ F` of two functors `F G : C ⥤ V` admitting Day
convolutions, and proves its naturality, both hexagon identities and, when `C` and `V` are
symmetric, its symmetry. Mathlib also equips the type synonym `C ⊛⥤ V` of `C ⥤ V` with the Day
convolution monoidal structure. This file combines the two: under the same existence and
colimit-preservation hypotheses as Mathlib's `MonoidalCategory (C ⊛⥤ V)`, it makes `C ⊛⥤ V` a
braided monoidal category when `C` and `V` are braided, and a symmetric monoidal category when
they are symmetric.

The transfer goes through the faithful functor `ι : (C ⊛⥤ V) ⥤ C ⥤ V` of a lawful Day
convolution monoidal structure, which Mathlib proves carries tensor products of morphisms and
associators to their Day convolution counterparts; the corresponding statements for whiskerings
and inverse associators are in
  `MathlibExt.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Basic`.

The main application is the symmetric monoidal category of symmetric sequences, Day convolution
along the block sum of the finite-bijection groupoid, over which symmetric spectra are modules.

## Main definitions

* `DayFunctor.braiding F G`: the Day convolution braiding `F ⊗ G ≅ G ⊗ F` in `C ⊛⥤ V`.
* The instances `BraidedCategory (C ⊛⥤ V)` and `SymmetricCategory (C ⊛⥤ V)`.

## Main statements

* `DayFunctor.η_app_comp_braiding_hom_natTrans_app`: the braiding is characterised by its
  restriction along the Day convolution unit `η F G`, where it is the braiding of `V` followed by
  `η G F` and the braiding of `C`.

## References

* B. Day, *On closed categories of functors*, Reports of the Midwest Category Seminar IV,
  Lecture Notes in Math. 137 (1970), 1-38.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct

noncomputable section

namespace DayFunctor

open LawfulDayConvolutionMonoidalCategoryStruct

attribute [local instance] convolution convolution₂ convolution₂'

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

section Braided

variable [BraidedCategory C] [BraidedCategory V]

/-- The Day convolution braiding `F ⊗ G ≅ G ⊗ F` of Day functors: Mathlib's
`DayConvolution.braiding` of the underlying functors. -/
def braiding (F G : C ⊛⥤ V) : F ⊗ G ≅ G ⊗ F :=
  (equiv C V).inverse.mapIso
    (DayConvolution.braiding ((ι C V (C ⊛⥤ V)).obj F) ((ι C V (C ⊛⥤ V)).obj G))

instance braidedCategory : BraidedCategory (C ⊛⥤ V) where
  braiding := braiding
  braiding_naturality_right F G H f := by
    apply (ι C V (C ⊛⥤ V)).map_injective
    simp only [Functor.map_comp, ι_map_whiskerLeft_eq_tensorHom,
      ι_map_whiskerRight_eq_tensorHom]
    exact DayConvolution.braiding_naturality_right _ _
  braiding_naturality_left f H := by
    apply (ι C V (C ⊛⥤ V)).map_injective
    simp only [Functor.map_comp, ι_map_whiskerLeft_eq_tensorHom,
      ι_map_whiskerRight_eq_tensorHom]
    exact DayConvolution.braiding_naturality_left _ _
  hexagon_forward F G H := by
    apply (ι C V (C ⊛⥤ V)).map_injective
    simp only [Functor.map_comp, ι_map_whiskerLeft_eq_tensorHom,
      ι_map_whiskerRight_eq_tensorHom, ι_map_associator_hom_eq_associator_hom]
    exact DayConvolution.hexagon_forward _ _ _
  hexagon_reverse F G H := by
    apply (ι C V (C ⊛⥤ V)).map_injective
    simp only [Functor.map_comp, ι_map_whiskerLeft_eq_tensorHom,
      ι_map_whiskerRight_eq_tensorHom, ι_map_associator_inv_eq_associator_inv]
    exact DayConvolution.hexagon_reverse _ _ _

/-- The braiding of the instance `BraidedCategory (C ⊛⥤ V)` is `DayFunctor.braiding`. -/
lemma braiding_eq (F G : C ⊛⥤ V) : β_ F G = braiding F G := (rfl)

/-- `ι` carries the braiding of Day functors to Mathlib's Day convolution braiding. -/
lemma ι_map_braiding_hom (F G : C ⊛⥤ V) :
    (ι C V (C ⊛⥤ V)).map (β_ F G).hom =
      (DayConvolution.braiding ((ι C V (C ⊛⥤ V)).obj F) ((ι C V (C ⊛⥤ V)).obj G)).hom :=
  (rfl)

/-- `ι` carries the inverse braiding of Day functors to Mathlib's inverse Day convolution
braiding. -/
lemma ι_map_braiding_inv (F G : C ⊛⥤ V) :
    (ι C V (C ⊛⥤ V)).map (β_ F G).inv =
      (DayConvolution.braiding ((ι C V (C ⊛⥤ V)).obj F) ((ι C V (C ⊛⥤ V)).obj G)).inv :=
  (rfl)

/-- The braiding of Day functors restricted along the Day convolution unit `η F G`: at `(x, y)`
it is the braiding of `V`, followed by `η G F` at `(y, x)` and the action of `G ⊗ F` on the
braiding of `C`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_braiding_hom_natTrans_app (F G : C ⊛⥤ V) (x y : C) :
    (η F G).app (x, y) ≫ (β_ F G).hom.natTrans.app (x ⊗ y) =
      (β_ _ _).hom ≫ (η G F).app (y, x) ≫ (G ⊗ F).functor.map (β_ y x).hom :=
  DayConvolution.unit_app_braiding_hom_app ((ι C V (C ⊛⥤ V)).obj F)
    ((ι C V (C ⊛⥤ V)).obj G) x y

/-- The inverse braiding of Day functors restricted along the Day convolution unit `η G F`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_braiding_inv_natTrans_app (F G : C ⊛⥤ V) (x y : C) :
    (η G F).app (x, y) ≫ (β_ F G).inv.natTrans.app (x ⊗ y) =
      (β_ _ _).inv ≫ (η F G).app (y, x) ≫ (F ⊗ G).functor.map (β_ x y).inv :=
  DayConvolution.unit_app_braiding_inv_app ((ι C V (C ⊛⥤ V)).obj F)
    ((ι C V (C ⊛⥤ V)).obj G) x y

end Braided

instance symmetricCategory [SymmetricCategory C] [SymmetricCategory V] :
    SymmetricCategory (C ⊛⥤ V) where
  symmetry F G := by
    apply (ι C V (C ⊛⥤ V)).map_injective
    rw [Functor.map_comp, Functor.map_id, ι_map_braiding_hom, ι_map_braiding_hom]
    exact DayConvolution.symmetry _ _

end DayFunctor

end

end CategoryTheory.MonoidalCategory
