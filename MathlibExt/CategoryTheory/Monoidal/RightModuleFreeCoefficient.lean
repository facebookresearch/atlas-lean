/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeEvaluation

/-!
# Actual free-unit and coefficient right modules

The coefficient tensor uses the existing right-module category. Its comparison
with the existing free functor and its Free-unit comparison retain the original
associators, unitors, multiplication, and both whole Hom functions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonObj MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion (RightModule)
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M]

/-- Construct an entire module isomorphism from an actual carrier isomorphism
whose forward arrow is proved right-linear. -/
def isoOfCarrier (X Y : RightModule M) (e : X.X ≅ Y.X)
    (h : X.action ≫ e.hom = (e.hom ▷ M) ≫ Y.action) : X ≅ Y where
  hom := Mod.Hom.mk' e.hom h
  inv :=
    Mod.Hom.mk' e.inv (by
        change Y.action ≫ e.inv = (e.inv ▷ M) ≫ X.action
        apply (cancel_mono e.hom).1
        simp only [Category.assoc]
        rw [e.inv_hom_id, Category.comp_id, h, ← comp_whiskerRight_assoc,
          e.inv_hom_id, id_whiskerRight, Category.id_comp])
  hom_inv_id := by apply Mod.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply Mod.hom_ext; exact e.inv_hom_id

/-- The complete forward value of the carrier isomorphism constructor. -/
@[simp]
theorem isoOfCarrier_hom (X Y : RightModule M) (e : X.X ≅ Y.X)
    (h : X.action ≫ e.hom = (e.hom ▷ M) ≫ Y.action) :
    (isoOfCarrier M X Y e h).hom.hom = e.hom := rfl

/-- The complete inverse value of the carrier isomorphism constructor. -/
@[simp]
theorem isoOfCarrier_inv (X Y : RightModule M) (e : X.X ≅ Y.X)
    (h : X.action ≫ e.hom = (e.hom ▷ M) ≫ Y.action) :
    (isoOfCarrier M X Y e h).inv.hom = e.inv := rfl

/-- The original stock regular module in the monoidal opposite, unwrapped on its carrier. -/
abbrev regularObject : RightModule M := unmopModule M (Mod.regular (mop M))

/-- The original regular carrier is the monoid object itself. -/
@[simp]
theorem regularObject_X : (regularObject M).X = M := rfl

/-- Its original whole right action is multiplication. -/
theorem regularObject_action : (regularObject M).action = μ[M] := rfl

/-- The actual ambient left unitor is right-linear from Free(unit) to regular(M). -/
theorem freeUnitRegular_hom_linear :
    (freeObject M (𝟙_ C)).action ≫ (λ_ M).hom =
      ((λ_ M).hom ▷ M) ≫ (regularObject M).action := by
  change ((α_ (𝟙_ C) M M).hom ≫ ((𝟙_ C) ◁ μ[M])) ≫ (λ_ M).hom =
    ((λ_ M).hom ▷ M) ≫ μ[M]
  rw [Category.assoc, leftUnitor_naturality]
  rw [leftUnitor_whiskerRight]
  simp only [Category.assoc]

/-- The entire free-unit module isomorphism is the actual ambient left unitor. -/
def freeUnitRegularIso : freeObject M (𝟙_ C) ≅ regularObject M :=
  isoOfCarrier M (freeObject M (𝟙_ C)) (regularObject M) (λ_ M)
    (freeUnitRegular_hom_linear M)

/-- The whole free-unit forward arrow is the original left unitor. -/
@[simp]
theorem freeUnitRegularIso_hom : (freeUnitRegularIso M).hom.hom = (λ_ M).hom := rfl

/-- The whole free-unit inverse arrow is the original inverse left unitor. -/
@[simp]
theorem freeUnitRegularIso_inv : (freeUnitRegularIso M).inv.hom = (λ_ M).inv := rfl

/-- The original free generator is sent to the complete original monoid unit. -/
@[reassoc]
theorem freeUnitRegularIso_generator :
    freeGenerator M (𝟙_ C) ≫ (freeUnitRegularIso M).hom.hom = η[M] := by
  have hu : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by monoidal
  change ((ρ_ (𝟙_ C)).inv ≫ ((𝟙_ C) ◁ η[M])) ≫ (λ_ M).hom = η[M]
  rw [Category.assoc, leftUnitor_naturality, ← Category.assoc, hu, Category.id_comp]

/-- Tensor an arbitrary coefficient with the complete actual right action. -/
abbrev coefficientTensor (P : C) (Y : RightModule M) : RightModule M where
  X := P ⊗ Y.X
  mod :=
    { smul := (α_ P Y.X M).hom ≫ (P ◁ Y.action)
      one_smul := by
        change ((P ⊗ Y.X) ◁ η[M]) ≫
          ((α_ P Y.X M).hom ≫ (P ◁ Y.action)) = (ρ_ (P ⊗ Y.X)).hom
        rw [associator_naturality_right_assoc, ← whiskerLeft_comp, Y.one_action]
        monoidal
      mul_smul := by
        change ((P ⊗ Y.X) ◁ μ[M]) ≫
            ((α_ P Y.X M).hom ≫ (P ◁ Y.action)) =
          (α_ (P ⊗ Y.X) M M).inv ≫
            (((α_ P Y.X M).hom ≫ (P ◁ Y.action)) ▷ M) ≫
              ((α_ P Y.X M).hom ≫ (P ◁ Y.action))
        have hp :
            (α_ (P ⊗ Y.X) M M).hom ≫ (α_ P Y.X (M ⊗ M)).hom ≫
                (P ◁ (α_ Y.X M M).inv) =
              ((α_ P Y.X M).hom ▷ M) ≫ (α_ P (Y.X ⊗ M) M).hom := by monoidal
        apply (cancel_epi (α_ (P ⊗ Y.X) M M).hom).1
        simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]
        rw [associator_naturality_right_assoc, associator_naturality_middle_assoc]
        rw [← whiskerLeft_comp, Y.mul_action]
        simp only [whiskerLeft_comp]
        slice_lhs 1 3 => rw [hp]
        simp only [Category.assoc] }

/-- The coefficient tensor retains its entire ambient tensor carrier. -/
@[simp]
theorem coefficientTensor_X (P : C) (Y : RightModule M) :
    (coefficientTensor M P Y).X = P ⊗ Y.X := rfl

/-- The coefficient tensor retains the exact second-factor right action. -/
theorem coefficientTensor_action (P : C) (Y : RightModule M) :
    (coefficientTensor M P Y).action = (α_ P Y.X M).hom ≫ (P ◁ Y.action) := rfl

/-- Every whole coefficient and module arrow induces its original tensor map. -/
def coefficientTensorMap {P P' : C} {Y Y' : RightModule M}
    (f : P ⟶ P') (g : Y ⟶ Y') :
    coefficientTensor M P Y ⟶ coefficientTensor M P' Y' :=
  Mod.Hom.mk' (f ⊗ₘ g.hom) (by
    have ha :
        ((f ⊗ₘ g.hom) ▷ M) ≫ (α_ P' Y'.X M).hom =
          (α_ P Y.X M).hom ≫ (f ⊗ₘ (g.hom ▷ M)) := by
      simpa only [tensorHom_id] using associator_naturality f g.hom (𝟙 M)
    change ((α_ P Y.X M).hom ≫ (P ◁ Y.action)) ≫ (f ⊗ₘ g.hom) =
      ((f ⊗ₘ g.hom) ▷ M) ≫ ((α_ P' Y'.X M).hom ≫ (P' ◁ Y'.action))
    simp only [Category.assoc]
    calc
      _ = (α_ P Y.X M).hom ≫ (f ⊗ₘ (Y.action ≫ g.hom)) := by
        rw [← id_tensorHom P Y.action, tensorHom_comp_tensorHom, Category.id_comp]
      _ = (α_ P Y.X M).hom ≫ (f ⊗ₘ ((g.hom ▷ M) ≫ Y'.action)) := by
        rw [CommutativeModuleConversion.RightModule.comm g]
      _ = (α_ P Y.X M).hom ≫ (f ⊗ₘ (g.hom ▷ M)) ≫ (P' ◁ Y'.action) := by
        rw [← id_tensorHom P' Y'.action, tensorHom_comp_tensorHom, Category.comp_id]
      _ = _ := by
        simpa only [Category.assoc] using
          (congrArg (fun k => k ≫ (P' ◁ Y'.action)) ha).symm)

/-- The full coefficient-tensor map function has the original ambient tensor value. -/
theorem coefficientTensorMap_hom {P P' : C} {Y Y' : RightModule M}
    (f : P ⟶ P') (g : Y ⟶ Y') :
    (coefficientTensorMap M f g).hom = f ⊗ₘ g.hom := rfl

/-- The whole coefficient tensor map respects both identity inputs. -/
@[simp]
theorem coefficientTensorMap_id (P : C) (Y : RightModule M) :
    coefficientTensorMap M (𝟙 P) (𝟙 Y) = 𝟙 (coefficientTensor M P Y) := by
  apply Mod.hom_ext
  simp only [coefficientTensorMap_hom, Mod.id_hom', id_tensorHom_id]

/-- The whole coefficient tensor map respects both complete input composites. -/
theorem coefficientTensorMap_comp {P P' P'' : C} {Y Y' Y'' : RightModule M}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    coefficientTensorMap M (f ≫ f') (g ≫ g') =
      coefficientTensorMap M f g ≫ coefficientTensorMap M f' g' := by
  apply Mod.hom_ext
  simp only [coefficientTensorMap_hom, Mod.comp_hom', tensorHom_comp_tensorHom]

/-- The actual whole coefficient-tensor family is a functor of both inputs. -/
def coefficientTensorPairFunctor : C × RightModule M ⥤ RightModule M where
  obj P := coefficientTensor M P.1 P.2
  map f := coefficientTensorMap M f.1 f.2
  map_id P := coefficientTensorMap_id M P.1 P.2
  map_comp f g := coefficientTensorMap_comp M f.1 g.1 f.2 g.2

/-- The actual associator identifies a coefficient tensor of a free module
with the complete free module on the coefficient tensor. -/
def coefficientFreeIso (P Q : C) :
    coefficientTensor M P (freeObject M Q) ≅ freeObject M (P ⊗ Q) :=
  isoOfCarrier M (coefficientTensor M P (freeObject M Q))
    (freeObject M (P ⊗ Q)) (α_ P Q M).symm (by
      have hp :
          (α_ P (Q ⊗ M) M).hom ≫ (P ◁ (α_ Q M M).hom) ≫
              (α_ P Q (M ⊗ M)).inv =
            ((α_ P Q M).inv ▷ M) ≫ (α_ (P ⊗ Q) M M).hom := by monoidal
      change ((α_ P (Q ⊗ M) M).hom ≫
          (P ◁ ((α_ Q M M).hom ≫ (Q ◁ μ[M])))) ≫ (α_ P Q M).inv =
        ((α_ P Q M).inv ▷ M) ≫ ((α_ (P ⊗ Q) M M).hom ≫ ((P ⊗ Q) ◁ μ[M]))
      simp only [whiskerLeft_comp, Category.assoc]
      rw [associator_inv_naturality_right]
      slice_lhs 1 3 => rw [hp]
      simp only [Category.assoc])

/-- The entire forward coefficient-free comparison is the original inverse associator. -/
@[simp]
theorem coefficientFreeIso_hom (P Q : C) :
    (coefficientFreeIso M P Q).hom.hom = (α_ P Q M).inv := rfl

/-- The entire inverse coefficient-free comparison is the original associator. -/
@[simp]
theorem coefficientFreeIso_inv (P Q : C) :
    (coefficientFreeIso M P Q).inv.hom = (α_ P Q M).hom := rfl

/-- Both complete coefficient arrows are respected by the coefficient-free comparison. -/
@[reassoc]
theorem coefficientFreeIso_naturality {P P' Q Q' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    coefficientTensorMap M f (freeMap M g) ≫ (coefficientFreeIso M P' Q').hom =
      (coefficientFreeIso M P Q).hom ≫ freeMap M (f ⊗ₘ g) := by
  apply Mod.hom_ext
  change (f ⊗ₘ (g ▷ M)) ≫ (α_ P' Q' M).inv =
    (α_ P Q M).inv ≫ ((f ⊗ₘ g) ▷ M)
  simpa only [tensorHom_id] using associator_inv_naturality f g (𝟙 M)

/-- The entire coefficient-free inverse is natural under both coefficient arrows. -/
@[reassoc]
theorem coefficientFreeIso_inv_naturality {P P' Q Q' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (coefficientFreeIso M P Q).inv ≫ coefficientTensorMap M f (freeMap M g) =
      freeMap M (f ⊗ₘ g) ≫ (coefficientFreeIso M P' Q').inv := by
  apply (cancel_mono (coefficientFreeIso M P' Q').hom).1
  simp only [Category.assoc, coefficientFreeIso_naturality, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The original tensor generator agrees with inserting the unit in the second factor. -/
@[reassoc]
theorem freeGenerator_associator (P Q : C) :
    freeGenerator M (P ⊗ Q) ≫ (α_ P Q M).hom = P ◁ freeGenerator M Q := by
  have hu : (ρ_ (P ⊗ Q)).inv ≫ (α_ P Q (𝟙_ C)).hom = P ◁ (ρ_ Q).inv := by
    monoidal
  change ((ρ_ (P ⊗ Q)).inv ≫ ((P ⊗ Q) ◁ η[M])) ≫ (α_ P Q M).hom =
    P ◁ ((ρ_ Q).inv ≫ (Q ◁ η[M]))
  rw [Category.assoc, associator_naturality_right, ← Category.assoc, hu,
    ← whiskerLeft_comp]

/-- Every actual free identity map is the complete module identity. -/
theorem freeMap_id (P : C) : freeMap M (𝟙 P) = 𝟙 (freeObject M P) :=
  (functor M).map_id P

/-- Every actual free composite map retains the two complete module arrows. -/
theorem freeMap_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
    freeMap M (f ≫ g) = freeMap M f ≫ freeMap M g :=
  (functor M).map_comp f g

/-- The full original free generator is natural under every coefficient arrow. -/
@[reassoc]
theorem freeGenerator_naturality {P P' : C} (f : P ⟶ P') :
    freeGenerator M P ≫ (f ▷ M) = f ≫ freeGenerator M P' := by
  have h := (adjunction M).unit_naturality f
  change (adjunction M).unit.app P ≫ (f ▷ M) = f ≫ (adjunction M).unit.app P' at h
  exact (congrArg (fun k => k ≫ (f ▷ M)) (adjunction_unit M P)).symm.trans
    (h.trans (congrArg (fun k => f ≫ k) (adjunction_unit M P')))

/-- The full original free extension is natural under every target module arrow. -/
theorem extendFree_naturality_right (P : C) {Y Y' : RightModule M}
    (f : P ⟶ Y.X) (g : Y ⟶ Y') :
    extendFree M P Y' (f ≫ g.hom) = extendFree M P Y f ≫ g :=
  (adjunction M).homEquiv_naturality_right_symm f g

/-- The original generator and multiplication action recover the whole free carrier. -/
theorem freeGenerator_action (X : C) :
    (freeGenerator M X ▷ M) ≫ (freeObject M X).action = 𝟙 (X ⊗ M) := by
  change (((ρ_ X).inv ≫ (X ◁ η[M])) ▷ M) ≫
    ((α_ X M M).hom ≫ (X ◁ μ[M])) = 𝟙 (X ⊗ M)
  rw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp, MonObj.one_mul, triangle_assoc_comp_right_inv_assoc]
  exact whiskerLeft_inv_hom _ _

/-- Pointwise carrier readback of the original complete extension function. -/
@[simp]
theorem extendFree_hom_apply (X : C) (Y : RightModule M) (f : X ⟶ Y.X) :
    (extendFree M X Y f).hom = (f ▷ M) ≫ Y.action :=
  congrFun (extendFree_hom M X Y) f

end CategoryTheory.RightModuleFree
