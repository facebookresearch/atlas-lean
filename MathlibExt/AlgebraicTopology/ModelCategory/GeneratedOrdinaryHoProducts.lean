/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoBinaryProduct

/-!
# Binary products on all original ordinary-Ho objects

Both target objects retain the original R replacements and actual
localization preimage Isos. The SAME product of those fibrant targets
has both original projections followed by the SAME inverse comparison
maps. The full original limiting fan constructs all Ho binary products.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.GeneratedOrdinaryHoProducts

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

/-- Both target objects retain the SAME original R source object. -/
def targetObject (T : HomotopyCategory C) : C :=
  (GeneratedFunctorialReplacements.R g).obj (OrdinaryHoBinaryProduct.sourceObject T)

/-- Target fibrancy is EARNED from the original R factory. -/
theorem target_isFibrant (T : HomotopyCategory C) : IsFibrant (targetObject g T) :=
  GeneratedFunctorialReplacements.R_isFibrant g _

/-- The full original R unit and original preimage Iso supply both actual target comparison functions. -/
def targetIso (T : HomotopyCategory C) : T ≅ (toHomotopyCategory C).obj (targetObject g T) := by
  let : (toHomotopyCategory C).EssSurj := Localization.essSurj (toHomotopyCategory C) (weakEquivalences C)
  let : IsIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app
      (OrdinaryHoBinaryProduct.sourceObject T))) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.unit_weak g _)
  exact ((toHomotopyCategory C).objObjPreimageIso T).symm ≪≫
    asIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app
      (OrdinaryHoBinaryProduct.sourceObject T)))

/-- The same specified pair uses the actual product of its TWO original R targets. -/
def product (Y Z : HomotopyCategory C) : HomotopyCategory C :=
  (toHomotopyCategory C).obj (targetObject g Y ⨯ targetObject g Z)

/-- Both full original projection functions retain the same two inverse original target Isos. -/
def fan (Y Z : HomotopyCategory C) : BinaryFan Y Z :=
  BinaryFan.mk
    ((toHomotopyCategory C).map (prod.fst : targetObject g Y ⨯ targetObject g Z ⟶ targetObject g Y) ≫
      (targetIso g Y).inv)
    ((toHomotopyCategory C).map (prod.snd : targetObject g Y ⨯ targetObject g Z ⟶ targetObject g Z) ≫
      (targetIso g Z).inv)

/-- Every caller pair retains both original target comparisons in its full actual product lift. -/
def lift {T Y Z : HomotopyCategory C} (f : T ⟶ Y) (h : T ⟶ Z) : T ⟶ product g Y Z := by
  let : IsFibrant (targetObject g Y) := target_isFibrant g Y
  let : IsFibrant (targetObject g Z) := target_isFibrant g Z
  exact OrdinaryHoBinaryProduct.lift g (targetObject g Y) (targetObject g Z)
    (f ≫ (targetIso g Y).hom) (h ≫ (targetIso g Z).hom)

/-- The first original projection reads back the same original caller map. -/
theorem lift_fst {T Y Z : HomotopyCategory C} (f : T ⟶ Y) (h : T ⟶ Z) :
    lift g f h ≫ (fan g Y Z).fst = f := by
  let : IsFibrant (targetObject g Y) := target_isFibrant g Y
  let : IsFibrant (targetObject g Z) := target_isFibrant g Z
  unfold lift fan
  change OrdinaryHoBinaryProduct.lift g (targetObject g Y) (targetObject g Z)
      (f ≫ (targetIso g Y).hom) (h ≫ (targetIso g Z).hom) ≫
    ((OrdinaryHoBinaryProduct.fan (targetObject g Y) (targetObject g Z)).fst ≫ (targetIso g Y).inv) = f
  rw [← Category.assoc, OrdinaryHoBinaryProduct.lift_fst, Category.assoc,
    (targetIso g Y).hom_inv_id, Category.comp_id]

/-- The second original projection reads back the same original caller map. -/
theorem lift_snd {T Y Z : HomotopyCategory C} (f : T ⟶ Y) (h : T ⟶ Z) :
    lift g f h ≫ (fan g Y Z).snd = h := by
  let : IsFibrant (targetObject g Y) := target_isFibrant g Y
  let : IsFibrant (targetObject g Z) := target_isFibrant g Z
  unfold lift fan
  change OrdinaryHoBinaryProduct.lift g (targetObject g Y) (targetObject g Z)
      (f ≫ (targetIso g Y).hom) (h ≫ (targetIso g Z).hom) ≫
    ((OrdinaryHoBinaryProduct.fan (targetObject g Y) (targetObject g Z)).snd ≫ (targetIso g Z).inv) = h
  rw [← Category.assoc, OrdinaryHoBinaryProduct.lift_snd, Category.assoc,
    (targetIso g Z).hom_inv_id, Category.comp_id]

/-- The two complete original product projection functions determine every original Ho map uniquely. -/
theorem hom_ext {T Y Z : HomotopyCategory C} (f h : T ⟶ product g Y Z)
    (hf : f ≫ (fan g Y Z).fst = h ≫ (fan g Y Z).fst)
    (hh : f ≫ (fan g Y Z).snd = h ≫ (fan g Y Z).snd) : f = h := by
  let : IsFibrant (targetObject g Y) := target_isFibrant g Y
  let : IsFibrant (targetObject g Z) := target_isFibrant g Z
  apply OrdinaryHoBinaryProduct.hom_ext g (targetObject g Y) (targetObject g Z)
  · apply (cancel_mono (targetIso g Y).inv).mp
    exact (Category.assoc _ _ _).trans (hf.trans (Category.assoc _ _ _).symm)
  · apply (cancel_mono (targetIso g Z).inv).mp
    exact (Category.assoc _ _ _).trans (hh.trans (Category.assoc _ _ _).symm)

/-- The actual original pair fan is limiting on the SAME all-Ho carrier. -/
def isLimitFan (Y Z : HomotopyCategory C) : IsLimit (fan g Y Z) :=
  BinaryFan.IsLimit.mk _ (lift g) (lift_fst g) (lift_snd g)
    (fun f h m hm₁ hm₂ => hom_ext g m (lift g f h)
      (hm₁.trans (lift_fst g f h).symm) (hm₂.trans (lift_snd g f h).symm))

include g in
/-- The same full original limiting fan supplies binary product existence on EVERY original pair. -/
theorem hasBinaryProduct (Y Z : HomotopyCategory C) : HasBinaryProduct Y Z :=
  ⟨⟨fan g Y Z, isLimitFan g Y Z⟩⟩

include g in
/-- The original R-target products supply the whole binary-products interface on the SAME ordinary Ho. -/
theorem hasBinaryProducts : HasBinaryProducts (HomotopyCategory C) := by
  let (Y Z : HomotopyCategory C) : HasBinaryProduct Y Z := hasBinaryProduct g Y Z
  exact hasBinaryProducts_of_hasLimit_pair _

end HomotopicalAlgebra.GeneratedOrdinaryHoProducts
