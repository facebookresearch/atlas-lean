/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableIntegerHom
import MathlibExt.CategoryTheory.Equivalence.IntegerAddition
import MathlibExt.CategoryTheory.Preadditive.HomIsoExact

/-!
# Actual source-shifted represented groups in the original ordinary stable model

Every integer source shift uses the same original suspension equivalence.
Its native power adjunction retains the original units and counits. The
actual inverse-power comparison gives both full Hom functions to the
negative target degree, on every original source and target morphism.
The specified generator family is retained; no unit-generator or weak
detection outcome is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v uI
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableSourceShiftHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "eOrd" => OrdinaryStableHoAdditive.equivalence g

/-- The original framing equivalence constructs all integer shifts with full coherent addition. -/
@[instance_reducible]
def hasShift : HasShift (HomotopyCategory C) ℤ :=
  Equivalence.IntegerOrbit.nativeHasShift eOrd

/-- The entire integer shift functor is the original ordinary power on all objects and arrows. -/
theorem shiftFunctor_eq (n : ℤ) :
    letI := hasShift g
    shiftFunctor (HomotopyCategory C) n = OrdinaryStableIntegerHom.shift g n := by
  unfold OrdinaryStableIntegerHom.shift
  exact Equivalence.IntegerOrbit.native_shiftFunctor eOrd n

/-- Every actual integer shift is additive for the original ordinary-stable Hom operations. -/
theorem shiftFunctor_additive (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    letI := hasShift g
    (shiftFunctor (HomotopyCategory C) n).Additive := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let := hasShift g
  let : (eOrd).functor.Additive := OrdinaryStableHoAdditive.suspension_additive g
  exact Equivalence.IntegerSuccessor.additive eOrd n

/-- The full source-shift functor is the same actual native power, with its identity comparison. -/
def shiftIso (n : ℤ) : OrdinaryStableIntegerHom.shift g n ≅ (eOrd ^ n).functor := by
  unfold OrdinaryStableIntegerHom.shift
  exact Iso.refl _

/-- The inverse of the original native ordinary shift power is the actual negative shift. -/
def inverseShiftIso (n : ℤ) :
    (eOrd ^ n).inverse ≅ OrdinaryStableIntegerHom.shift g (-n) := by
  unfold OrdinaryStableIntegerHom.shift
  exact Equivalence.IntegerAddition.inversePower eOrd n

/-- The complete represented Hom group type shifts the original source. -/
abbrev hom (n : ℤ) (X E : HomotopyCategory C) :=
  (OrdinaryStableIntegerHom.shift g n).obj X ⟶ E

/-- Every source-shifted Hom has the same actual ordinary-stable additive group. -/
@[instance_reducible]
def homGroup (n : ℤ) (X E : HomotopyCategory C) : AddCommGroup (hom g n X E) :=
  OrdinaryStableHoPreadditive.homGroup g ((OrdinaryStableIntegerHom.shift g n).obj X) E

/-- Both original power-adjunct functions give the source/negative-target additive Hom equivalence. -/
def homEquiv (n : ℤ) (X E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n X E ≃+ OrdinaryStableIntegerHom.hom g (-n) X E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let : (eOrd).functor.Additive := OrdinaryStableHoAdditive.suspension_additive g
  let : (eOrd ^ n).functor.Additive := Equivalence.IntegerSuccessor.additive eOrd n
  exact (Preadditive.HomIsoExact.homIso ((shiftIso g n).app X) (Iso.refl E)).trans
    (((eOrd ^ n).toAdjunction.homAddEquiv X E).trans
      (Preadditive.HomIsoExact.homIso (Iso.refl X) ((inverseShiftIso g n).app E)))

/-- The entire forward function is the actual native power adjunct and original inverse comparison. -/
theorem homEquiv_apply (n : ℤ) (X E : HomotopyCategory C) (f : hom g n X E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homEquiv g n X E f = (eOrd ^ n).toAdjunction.homEquiv X E
        ((shiftIso g n).inv.app X ≫ f) ≫
      (inverseShiftIso g n).hom.app E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  unfold homEquiv
  simp only [AddEquiv.trans_apply, Preadditive.HomIsoExact.homIso_apply, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp]
  rfl

/-- The complete inverse function retains the same power inverse adjunct and comparison inverse. -/
theorem homEquiv_symm_apply (n : ℤ) (X E : HomotopyCategory C)
    (f : OrdinaryStableIntegerHom.hom g (-n) X E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (homEquiv g n X E).symm f = (shiftIso g n).hom.app X ≫
      ((eOrd ^ n).toAdjunction.homEquiv X E).symm
        (f ≫ (inverseShiftIso g n).inv.app E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let : (eOrd).functor.Additive := OrdinaryStableHoAdditive.suspension_additive g
  let : (eOrd ^ n).functor.Additive := Equivalence.IntegerSuccessor.additive eOrd n
  unfold homEquiv
  change (Preadditive.HomIsoExact.homIso ((shiftIso g n).app X) (Iso.refl E)).symm
      (((eOrd ^ n).toAdjunction.homAddEquiv X E).symm
        ((Preadditive.HomIsoExact.homIso (Iso.refl X) ((inverseShiftIso g n).app E)).symm f)) = _
  rw [Preadditive.HomIsoExact.homIso_symm_apply, Preadditive.HomIsoExact.homIso_symm_apply]
  simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp]
  rfl

/-- Every original source arrow commutes with both actual source-shift Hom functions. -/
theorem homEquiv_source (n : ℤ) {X X' : HomotopyCategory C} (a : X' ⟶ X)
    (E : HomotopyCategory C) (f : hom g n X E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homEquiv g n X' E ((OrdinaryStableIntegerHom.shift g n).map a ≫ f) =
      a ≫ homEquiv g n X E f := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [homEquiv_apply, homEquiv_apply]
  rw [← Category.assoc, ← (shiftIso g n).inv.naturality a, Category.assoc,
    Adjunction.homEquiv_naturality_left, Category.assoc]

/-- Every original target arrow retains the actual negative ordinary-shift map. -/
theorem homEquiv_target (n : ℤ) (X : HomotopyCategory C) {E E' : HomotopyCategory C}
    (a : E ⟶ E') (f : hom g n X E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homEquiv g n X E' (f ≫ a) =
      homEquiv g n X E f ≫ (OrdinaryStableIntegerHom.shift g (-n)).map a := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [homEquiv_apply, homEquiv_apply, ← Category.assoc, Adjunction.homEquiv_naturality_right,
    Category.assoc, (inverseShiftIso g n).hom.naturality, ← Category.assoc]

/-- Every label in the specified original family retains every actual integer source shift. -/
abbrev generatorHom {I : Type uI} (G : I → HomotopyCategory C)
    (n : ℤ) (i : I) (E : HomotopyCategory C) := hom g n (G i) E

/-- The entire original family has the actual source/negative-target represented equivalence. -/
def generatorHomEquiv {I : Type uI} (G : I → HomotopyCategory C)
    (n : ℤ) (i : I) (E : HomotopyCategory C) :=
  homEquiv g n (G i) E

end HomotopicalAlgebra.OrdinaryStableSourceShiftHom
