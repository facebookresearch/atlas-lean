/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoFibrantProduct

import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationFibrantProducts

/-!
# Original fibrant products and their full ordinary-Ho limiting fan

Every source Ho object is presented by its SAME original Q and the
original localization preimage comparison. The actual product Hom lift
on that cofibrant presentation gives the whole caller's lift. Both
original product projections and full original source Iso functions are
retained, proving the actual limiting fan in ordinary Ho.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryHoBinaryProduct

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

/-- The original source preimage remains on the unchanged original model carrier. -/
def sourceObject (T : HomotopyCategory C) : C := by
  let : (toHomotopyCategory C).EssSurj := Localization.essSurj (toHomotopyCategory C) (weakEquivalences C)
  exact (toHomotopyCategory C).objPreimage T

/-- The actual original Q of that original source object. -/
def cofibrantSource (T : HomotopyCategory C) : C :=
  (GeneratedFunctorialReplacements.Q g).obj (sourceObject T)

/-- Source cofibrancy is earned from the SAME original Q factory. -/
theorem source_isCofibrant (T : HomotopyCategory C) : IsCofibrant (cofibrantSource g T) :=
  GeneratedFunctorialReplacements.Q_isCofibrant g _

/-- Both full original source comparison functions retain the original Q counit and preimage Iso. -/
def sourceIso (T : HomotopyCategory C) : (toHomotopyCategory C).obj (cofibrantSource g T) ≅ T := by
  let : (toHomotopyCategory C).EssSurj := Localization.essSurj (toHomotopyCategory C) (weakEquivalences C)
  let : IsIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app (sourceObject T))) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.counit_weak g _)
  exact asIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app (sourceObject T))) ≪≫
    (toHomotopyCategory C).objObjPreimageIso T

variable (Y Z : C) [IsFibrant Y] [IsFibrant Z]

/-- The actual original product point and BOTH complete original projection maps. -/
def fan : BinaryFan ((toHomotopyCategory C).obj Y) ((toHomotopyCategory C).obj Z) :=
  BinaryFan.mk ((toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y))
    ((toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z))

/-- Every original caller pair is lifted through the SAME original cofibrant-source Iso. -/
def lift {T : HomotopyCategory C} (f : T ⟶ (toHomotopyCategory C).obj Y)
    (h : T ⟶ (toHomotopyCategory C).obj Z) : T ⟶ (toHomotopyCategory C).obj (Y ⨯ Z) := by
  let : IsCofibrant (cofibrantSource g T) := source_isCofibrant g T
  exact (sourceIso g T).inv ≫ OrdinaryHoFibrantProduct.lift (cofibrantSource g T) Y Z
    ((sourceIso g T).hom ≫ f) ((sourceIso g T).hom ≫ h)

/-- The original first Ho projection reads back the caller's original first map. -/
theorem lift_fst {T : HomotopyCategory C} (f : T ⟶ (toHomotopyCategory C).obj Y)
    (h : T ⟶ (toHomotopyCategory C).obj Z) :
    lift g Y Z f h ≫ (fan Y Z).fst = f := by
  let : IsCofibrant (cofibrantSource g T) := source_isCofibrant g T
  unfold lift fan
  change ((sourceIso g T).inv ≫ OrdinaryHoFibrantProduct.lift (cofibrantSource g T) Y Z
      ((sourceIso g T).hom ≫ f) ((sourceIso g T).hom ≫ h)) ≫
    (toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y) = f
  rw [Category.assoc, OrdinaryHoFibrantProduct.lift_fst]
  exact (sourceIso g T).inv_hom_id_assoc f

/-- The original second Ho projection reads back the caller's original second map. -/
theorem lift_snd {T : HomotopyCategory C} (f : T ⟶ (toHomotopyCategory C).obj Y)
    (h : T ⟶ (toHomotopyCategory C).obj Z) :
    lift g Y Z f h ≫ (fan Y Z).snd = h := by
  let : IsCofibrant (cofibrantSource g T) := source_isCofibrant g T
  unfold lift fan
  change ((sourceIso g T).inv ≫ OrdinaryHoFibrantProduct.lift (cofibrantSource g T) Y Z
      ((sourceIso g T).hom ≫ f) ((sourceIso g T).hom ≫ h)) ≫
    (toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z) = h
  rw [Category.assoc, OrdinaryHoFibrantProduct.lift_snd]
  exact (sourceIso g T).inv_hom_id_assoc h

include g in
/-- Both complete original product projection functions jointly determine EVERY source Ho map. -/
theorem hom_ext {T : HomotopyCategory C} (f h : T ⟶ (toHomotopyCategory C).obj (Y ⨯ Z))
    (hf : f ≫ (fan Y Z).fst = h ≫ (fan Y Z).fst)
    (hh : f ≫ (fan Y Z).snd = h ≫ (fan Y Z).snd) : f = h := by
  change f ≫ (toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y) =
    h ≫ (toHomotopyCategory C).map (prod.fst : Y ⨯ Z ⟶ Y) at hf
  change f ≫ (toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z) =
    h ≫ (toHomotopyCategory C).map (prod.snd : Y ⨯ Z ⟶ Z) at hh
  let : IsCofibrant (cofibrantSource g T) := source_isCofibrant g T
  apply (cancel_epi (sourceIso g T).hom).mp
  exact ModelLocalization.product_hom_ext (toHomotopyCategory C) Y Z
    ((sourceIso g T).hom ≫ f) ((sourceIso g T).hom ≫ h)
    (by simpa only [Category.assoc] using congrArg (fun x => (sourceIso g T).hom ≫ x) hf)
    (by simpa only [Category.assoc] using congrArg (fun x => (sourceIso g T).hom ≫ x) hh)

/-- The actual original limiting fan satisfies the full original universal property in ordinary Ho. -/
def isLimitFan : IsLimit (fan Y Z) :=
  BinaryFan.IsLimit.mk _ (lift g Y Z) (lift_fst g Y Z) (lift_snd g Y Z)
    (fun f h m hm₁ hm₂ =>
      ModelLocalization.product_hom_ext (toHomotopyCategory C) Y Z m (lift g Y Z f h)
        (hm₁.trans (lift_fst g Y Z f h).symm) (hm₂.trans (lift_snd g Y Z f h).symm))

end HomotopicalAlgebra.OrdinaryHoBinaryProduct
