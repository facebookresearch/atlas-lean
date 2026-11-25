/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeTensor
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndEvaluation
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Right-module mapping from the regular module

The regular right module is the tensor unit. Right-adjoint uniqueness
identifies its mapping functor with the identity, and the original
balanced quotient projection computes the carrier of this comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

section RegularMappingSource

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uC vC
open CategoryTheory MonoidalCategory Limits BraidedCategory
open CategoryTheory.CommutativeModuleConversion (RightModule)
open scoped MonoidalClosed

namespace CategoryTheory.RightModuleMappingEnd.Regular

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (R : C) [MonObj R] [IsCommMonObj R]
/-- The actual relative tensor structure on right modules. -/
local instance : MonoidalCategory (RightModule R) := RightModuleFree.tensorMonoidal R
/-- The actual transported symmetry of the relative tensor. -/
local instance : SymmetricCategory (RightModule R) := RightModuleFree.tensorSymmetric R

/-- Tensoring with the actual regular module is naturally the original identity functor. -/
def regularTensorIso : tensorRight (RightModuleFree.regularObject R) ≅ 𝟭 (RightModule R) :=
  (curriedTensor (RightModule R)).flip.mapIso (RightModuleFree.regularTensorUnitIso R) ≪≫
    rightUnitorNatIso (RightModule R)

/-- The actual tensor unit supplies its complete identity adjunction. -/
def regularUnitAdjunction : tensorRight (RightModuleFree.regularObject R) ⊣ 𝟭 (RightModule R) :=
  Adjunction.id.ofNatIsoLeft (regularTensorIso R).symm

/-- Right-adjoint uniqueness identifies the actual regular Mapping_R functor with identity. -/
def regularMappingNatIso :
    RightModuleMappingEnd.functor R (RightModuleFree.regularObject R) ≅ 𝟭 (RightModule R) :=
  Adjunction.rightAdjointUniq
    (RightModuleMappingEnd.adjunction R (RightModuleFree.regularObject R))
    (regularUnitAdjunction R)

/-- Both original stock module maps evaluate the complete regular-module mapping equalizer. -/
def regularMappingIso (N : RightModule R) :
    RightModuleMappingEnd.moduleObject R (RightModuleFree.regularObject R) N ≅ N :=
  (regularMappingNatIso R).app N

omit [HasEqualizers C] in
/-- The original balanced quotient projection computes the complete regular tensor evaluation. -/
@[reassoc]
theorem regularTensorIso_hom_π (N : RightModule R) :
    RightModuleFree.relativeTensorπ R N (RightModuleFree.regularObject R) ≫
      ((regularTensorIso R).hom.app N).hom = N.action := by
  change RightModuleFree.relativeTensorπ R N (RightModuleFree.regularObject R) ≫
    ((N ◁ (RightModuleFree.regularTensorUnitIso R).hom).hom ≫ (ρ_ N).hom.hom) = _
  rw [← Category.assoc, RightModuleFree.relativeTensorWhiskerLeft_π,
    RightModuleFree.regularTensorUnitIso_hom]
  change (N.X ◁ 𝟙 R ≫ RightModuleFree.relativeTensorπ R N (𝟙_ (RightModule R))) ≫
    (ρ_ N).hom.hom = _
  rw [whiskerLeft_id, Category.id_comp, RightModuleFree.relativeTensorRightUnitor_hom_π]

omit [HasEqualizers C] in
/-- The actual regular-unit counit is the original full tensor-unit comparison. -/
theorem regularUnitAdjunction_counit (N : RightModule R) :
    (regularUnitAdjunction R).counit.app N = (regularTensorIso R).hom.app N := by
  change (regularTensorIso R).hom.app N ≫ 𝟙 N = _
  exact Category.comp_id _

/-- The regular mapping inverse has its actual original tensor-adjunction mate. -/
theorem regularMappingIso_inv_mate (N : RightModule R) :
    (tensorRight (RightModuleFree.regularObject R)).map (regularMappingIso R N).inv ≫
      (RightModuleMappingEnd.adjunction R (RightModuleFree.regularObject R)).counit.app N =
        (regularTensorIso R).hom.app N := by
  change (tensorRight (RightModuleFree.regularObject R)).map
    ((Adjunction.rightAdjointUniq
      (RightModuleMappingEnd.adjunction R (RightModuleFree.regularObject R))
      (regularUnitAdjunction R)).inv.app N) ≫ _ = _
  rw [Adjunction.rightAdjointUniq_inv_app, Adjunction.rightAdjointUniq_hom_app_counit]
  exact regularUnitAdjunction_counit R N

/-- The genuine regular evaluation inverse retains the original whole right-action transpose. -/
@[reassoc]
theorem regularMappingIso_inv_ι (N : RightModule R) :
    (regularMappingIso R N).inv.hom ≫
      RightModuleMappingEnd.ι R (RightModuleFree.regularObject R) N =
        MonoidalClosed.curry ((β_ R N.X).hom ≫ N.action) := by
  have hp := congrArg
    (fun q => RightModuleFree.relativeTensorπ R N (RightModuleFree.regularObject R) ≫ q.hom)
    (regularMappingIso_inv_mate R N)
  change RightModuleFree.relativeTensorπ R N (RightModuleFree.regularObject R) ≫
    ((tensorRight (RightModuleFree.regularObject R)).map (regularMappingIso R N).inv).hom ≫
      ((RightModuleMappingEnd.adjunction R (RightModuleFree.regularObject R)).counit.app N).hom =
        RightModuleFree.relativeTensorπ R N (RightModuleFree.regularObject R) ≫
          ((regularTensorIso R).hom.app N).hom at hp
  erw [RightModuleMappingEnd.tensorRight_map_π_assoc,
    RightModuleMappingEnd.adjunction_counit_π, regularTensorIso_hom_π] at hp
  change (regularMappingIso R N).inv.hom ▷ R ≫
    (β_ (RightModuleMappingEnd.moduleObject R (RightModuleFree.regularObject R) N).X R).hom ≫
      MonoidalClosed.uncurry (RightModuleMappingEnd.ι R (RightModuleFree.regularObject R) N) =
        N.action at hp
  rw [braiding_naturality_left_assoc, ← MonoidalClosed.uncurry_natural_left] at hp
  apply ((ihom.adjunction R).homEquiv _ _).symm.injective
  change MonoidalClosed.uncurry _ = MonoidalClosed.uncurry _
  rw [MonoidalClosed.uncurry_curry]
  calc
    MonoidalClosed.uncurry _ =
        (β_ R N.X).hom ≫ (β_ N.X R).hom ≫ MonoidalClosed.uncurry _ := by
      rw [SymmetricCategory.symmetry_assoc]
    _ = (β_ R N.X).hom ≫ N.action := by rw [hp]

omit [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [IsCommMonObj R] in
/-- Equal original source modules and equal whole isos retain their entire inverse carriers. -/
theorem inverseCarrier_heq {M M' N : RightModule R} (hM : M = M')
    (e : M ≅ N) (e' : M' ≅ N) (hE : HEq e e') : HEq e.inv.hom e'.inv.hom := by
  cases hM
  have h : e = e' := eq_of_heq hE
  cases h
  rfl

omit [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [IsCommMonObj R] in
/-- Equal whole original isos and inclusions retain their complete inverse-inclusion composite. -/
theorem inverseInclusion_eq {M M' N : RightModule R} (hM : M = M')
    (e : M ≅ N) (e' : M' ≅ N) (hE : HEq e e') (H : C)
    (i : M.X ⟶ H) (i' : M'.X ⟶ H) (hi : HEq i i') :
    e.inv.hom ≫ i = e'.inv.hom ≫ i' := by
  cases hM
  have he : e = e' := eq_of_heq hE
  have hi' : i = i' := eq_of_heq hi
  cases he
  cases hi'
  rfl

end CategoryTheory.RightModuleMappingEnd.Regular

end RegularMappingSource
