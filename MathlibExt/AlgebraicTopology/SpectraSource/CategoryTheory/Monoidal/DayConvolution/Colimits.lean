/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Colimits.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.ExternalProduct.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Colimits and Day convolution

Day convolution with a fixed left factor preserves colimits whenever left tensoring with
its values does. The proof factors convolution into the external product and left
Kan extension along the tensor functor. It does not require a closed monoidal structure.

The result applies to any lawful presentation of Day convolution whose interpretation functor
preserves and reflects the colimits in question. In particular it applies to symmetric
sequences, allowing colimits of modules over a sphere sequence to be formed on their carriers.

The Kan-extension comparison uses Mathlib's `Functor.lanAdjunction` and
`Functor.leftKanExtensionUnique`.

## References

* B. Day, *On closed categories of functors*, Reports of the Midwest Category Seminar IV,
  Lecture Notes in Mathematics 137 (1970), 1–38.
-/

public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Limits

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]
  {J : Type u₄} [Category.{v₄} J]

namespace LawfulDayConvolutionMonoidalCategoryStruct

variable (C V) (D : Type u₃) [Category.{v₃} D] [MonoidalCategory D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]
  [∀ F : C × C ⥤ V, (tensor C).HasLeftKanExtension F]

/-- Tensoring on the left in a lawful Day presentation is external product followed by
left Kan extension, after passing to underlying functors. -/
noncomputable def tensorLeftCompιIsoLan (d : D) :
    tensorLeft d ⋙ ι C V D ≅
      ι C V D ⋙ ((externalProductBifunctorCurried C C V).obj ((ι C V D).obj d) ⋙
        Functor.uncurry) ⋙ (tensor C).lan := by
  letI (d' : D) : ((ι C V D).obj (d ⊗ d')).IsLeftKanExtension
      (convolutionExtensionUnit C V d d') :=
    (isPointwiseLeftKanExtensionConvolutionExtensionUnit d d').isLeftKanExtension
  refine NatIso.ofComponents (fun d' ↦ Functor.leftKanExtensionUnique _
    (convolutionExtensionUnit C V d d')
      ((tensor C).lan.obj (((ι C V D).obj d) ⊠ ((ι C V D).obj d')))
      ((tensor C).lanUnit.app (((ι C V D).obj d) ⊠ ((ι C V D).obj d')))) ?_
  intro d' d'' f
  apply Functor.hom_ext_of_isLeftKanExtension _ (convolutionExtensionUnit C V d d')
  ext ⟨x, y⟩
  simp only [Functor.comp_map, Functor.leftKanExtensionUnique_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, tensor_obj, curriedTensor_obj_map]
  have fac (a : D) := Functor.descOfIsLeftKanExtension_fac_app
    ((ι C V D).obj (d ⊗ a)) (convolutionExtensionUnit C V d a)
    ((tensor C).lan.obj (((ι C V D).obj d) ⊠ ((ι C V D).obj a)))
    ((tensor C).lanUnit.app (((ι C V D).obj d) ⊠ ((ι C V D).obj a))) (x, y)
  simp only [tensor_obj] at fac
  rw [← Category.assoc, convolutionExtensionUnit_comp_ι_map_whiskerLeft_app,
    Category.assoc, fac, ← Category.assoc, fac]
  exact congr_app ((tensor C).lanUnit.naturality
    (((externalProductBifunctorCurried C C V).obj ((ι C V D).obj d) ⋙
      Functor.uncurry).map ((ι C V D).map f))) (x, y)

/-- The Kan-extension comparison respects the universal convolution maps. -/
@[reassoc (attr := simp)]
lemma convolutionExtensionUnit_comp_tensorLeftCompιIsoLan_hom_app
    (d d' : D) (x y : C) :
    (convolutionExtensionUnit C V d d').app (x, y) ≫
      ((tensorLeftCompιIsoLan C V D d).hom.app d').app (x ⊗ y) =
        ((tensor C).lanUnit.app (((ι C V D).obj d) ⊠ ((ι C V D).obj d'))).app (x, y) := by
  have : ((ι C V D).obj (d ⊗ d')).IsLeftKanExtension
      (convolutionExtensionUnit C V d d') :=
    (isPointwiseLeftKanExtensionConvolutionExtensionUnit d d').isLeftKanExtension
  simpa only [tensorLeftCompιIsoLan, NatIso.ofComponents_hom_app,
    Functor.leftKanExtensionUnique_hom, tensor_obj] using
    Functor.descOfIsLeftKanExtension_fac_app _ (convolutionExtensionUnit C V d d') _
      ((tensor C).lanUnit.app (((ι C V D).obj d) ⊠ ((ι C V D).obj d'))) (x, y)

/-- The inverse Kan-extension comparison recovers the universal convolution maps. -/
@[reassoc (attr := simp)]
lemma lanUnit_comp_tensorLeftCompιIsoLan_inv_app (d d' : D) (x y : C) :
    ((tensor C).lanUnit.app (((ι C V D).obj d) ⊠ ((ι C V D).obj d'))).app (x, y) ≫
      ((tensorLeftCompιIsoLan C V D d).inv.app d').app (x ⊗ y) =
        (convolutionExtensionUnit C V d d').app (x, y) := by
  exact (Iso.comp_inv_eq (((tensorLeftCompιIsoLan C V D d).app d').app (x ⊗ y))).2
    (convolutionExtensionUnit_comp_tensorLeftCompιIsoLan_hom_app C V D d d' x y).symm

/-- A lawful Day convolution preserves colimits on the left when its interpretation preserves
and reflects them, and the tensor product in the value category preserves them on the left. -/
lemma preservesColimitsOfShape_tensorLeft (d : D)
    [HasColimitsOfShape J V]
    [∀ x, PreservesColimitsOfShape J (tensorLeft (((ι C V D).obj d).obj x))]
    [PreservesColimitsOfShape J (ι C V D)] [ReflectsColimitsOfShape J (ι C V D)] :
    PreservesColimitsOfShape J (tensorLeft d) := by
  have := (tensor C).lanAdjunction V |>.isLeftAdjoint
  have : PreservesColimitsOfShape J (tensorLeft d ⋙ ι C V D) :=
    preservesColimitsOfShape_of_natIso (tensorLeftCompιIsoLan C V D d).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (tensorLeft d) (ι C V D)

end LawfulDayConvolutionMonoidalCategoryStruct

end CategoryTheory.MonoidalCategory
