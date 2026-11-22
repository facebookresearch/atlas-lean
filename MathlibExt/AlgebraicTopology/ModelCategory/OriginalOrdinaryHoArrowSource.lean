/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Actual original Q/R representatives of all ordinary-Ho arrows

The original localization supplies preimage objects and both full preimage
isomorphisms. The original generated Q and R give actual cofibrant source
and fibrant target objects. The native fundamental lemma constructs the
point-set representative of every full Ho morphism between them. Its
whole Arrow isomorphism retains both original comparison maps. Weakness
of that original model map is exactly invertibility of the given Ho arrow.
No strict functor of chosen representatives is asserted.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.OriginalOrdinaryHoArrowSource

variable {C : Type u} [Category.{v} C] [ModelCategory C]

local notation "H" => toHomotopyCategory C

/-- The source preimage is selected in the same original weak localization. -/
def preimage (X : HomotopyCategory C) : C := by
  letI : (H).EssSurj := Localization.essSurj (H) (weakEquivalences C)
  exact (H).objPreimage X

/-- The entire original preimage isomorphism retains both localization comparison functions. -/
def preimageIso (X : HomotopyCategory C) : (H).obj (preimage X) ≅ X := by
  letI : (H).EssSurj := Localization.essSurj (H) (weakEquivalences C)
  exact (H).objObjPreimageIso X

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

/-- Every actual source is the original Q of that original localization preimage. -/
def sourceObject (X : HomotopyCategory C) : C :=
  (GeneratedFunctorialReplacements.Q g).obj (preimage X)

/-- Every actual target is the original R of the same kind of original preimage. -/
def targetObject (Y : HomotopyCategory C) : C :=
  (GeneratedFunctorialReplacements.R g).obj (preimage Y)

/-- Original Q, with its original factorization choices, earns source cofibrancy. -/
theorem source_isCofibrant (X : HomotopyCategory C) : IsCofibrant (sourceObject g X) :=
  GeneratedFunctorialReplacements.Q_isCofibrant g (preimage X)

/-- The original R factory earns fibrancy of every actual representative target. -/
theorem target_isFibrant (Y : HomotopyCategory C) : IsFibrant (targetObject g Y) :=
  GeneratedFunctorialReplacements.R_isFibrant g (preimage Y)

/-- The actual source counit and entire original preimage Iso give both source comparison maps. -/
def sourceIso (X : HomotopyCategory C) : (H).obj (sourceObject g X) ≅ X := by
  letI : IsIso ((H).map ((GeneratedFunctorialReplacements.counit g).app (preimage X))) :=
    Localization.inverts (H) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.counit_weak g (preimage X))
  exact asIso ((H).map ((GeneratedFunctorialReplacements.counit g).app (preimage X))) ≪≫
    preimageIso X

/-- The original inverse R-unit and whole preimage Iso give both target comparison functions. -/
def targetIso (Y : HomotopyCategory C) : (H).obj (targetObject g Y) ≅ Y := by
  letI : IsIso ((H).map ((GeneratedFunctorialReplacements.unit g).app (preimage Y))) :=
    Localization.inverts (H) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.unit_weak g (preimage Y))
  exact (asIso ((H).map ((GeneratedFunctorialReplacements.unit g).app (preimage Y)))).symm ≪≫
    preimageIso Y

/-- The original fundamental lemma supplies an actual point-set map for every complete Ho arrow. -/
theorem exists_representative {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    ∃ a : sourceObject g X ⟶ targetObject g Y,
      (H).map a = (sourceIso g X).hom ≫ f ≫ (targetIso g Y).inv := by
  let := source_isCofibrant g X
  let := target_isFibrant g Y
  exact map_surjective_of_isLocalization (H) (sourceObject g X) (targetObject g Y)
    ((sourceIso g X).hom ≫ f ≫ (targetIso g Y).inv)

/-- The chosen actual map comes only from that original Q/R fundamental-lemma construction. -/
def representative {X Y : HomotopyCategory C} (f : X ⟶ Y) : sourceObject g X ⟶ targetObject g Y :=
  Classical.choose (exists_representative g f)

/-- Its whole Ho function is the original source comparison, caller map and inverse target comparison. -/
theorem representative_fac {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    (H).map (representative g f) = (sourceIso g X).hom ≫ f ≫ (targetIso g Y).inv :=
  Classical.choose_spec (exists_representative g f)

/-- Every full Ho arrow is an actual Arrow built from the same original point-set representative. -/
def sourceArrow {X Y : HomotopyCategory C} (f : X ⟶ Y) : Arrow C :=
  Arrow.mk (representative g f)

/-- The exact original model arrow and both original comparison Isos give a whole Arrow Iso. -/
def sourceArrowIso {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    Arrow.mk ((H).map (representative g f)) ≅ Arrow.mk f :=
  Arrow.isoMk' ((H).map (representative g f)) f (sourceIso g X) (targetIso g Y) (by
    change (sourceIso g X).hom ≫ f = (H).map (representative g f) ≫ (targetIso g Y).hom
    rw [representative_fac]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The original representative is weak exactly when the complete original Ho arrow is invertible. -/
theorem representative_weak_iff {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    weakEquivalences C (representative g f) ↔ IsIso f :=
  (weakEquivalence_iff_isIso_toHomotopyCategory_map _).trans
    ((MorphismProperty.isomorphisms (HomotopyCategory C)).arrow_mk_iso_iff (sourceArrowIso g f))

end HomotopicalAlgebra.OriginalOrdinaryHoArrowSource
