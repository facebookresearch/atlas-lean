/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoAdditive
import MathlibExt.CategoryTheory.Equivalence.IntegerSuccessor
import MathlibExt.CategoryTheory.Preadditive.HomIso

/-!
# Every integer ordinary suspension Hom group and its actual successor

The specified ordinary suspension equivalence retains the original framing
loop inverse, unit and counit. Its native powers give every integer object
and functor. The original Hom groups give all represented integer groups.
The complete successor comparison and original additive Hom adjunction
give the actual degree-one Hom comparison, natural in both arguments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableIntegerHom

private def postcompIso {D : Type*} [Category* D] [Preadditive D]
    {Y Y' : D} (e : Y ≅ Y') (X : D) : (X ⟶ Y) ≃+ (X ⟶ Y') :=
  Preadditive.HomIsoExact.homIso (Iso.refl X) e

private def stepFromAdjunction {D : Type*} [Category* D] [Preadditive D]
    {F G : D ⥤ D} (adj : F ⊣ G) [F.Additive] (X Y Y' : D) (e : Y ≅ G.obj Y') :
    (X ⟶ Y) ≃+ (F.obj X ⟶ Y') :=
  (postcompIso e X).trans (adj.homAddEquiv X Y').symm

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)
local notation "Ω" => DerivedSuspensionLoopAdjunction.loops
  (GeneratedFunctorialReplacements.fromGeneration g)
local notation "adjOrd" => DerivedSuspensionLoopAdjunction.adjunction
  (GeneratedFunctorialReplacements.fromGeneration g)

/-- Every integer shift is a native power of the SAME actual ordinary suspension/loop equivalence. -/
@[irreducible]
def shift (n : ℤ) : HomotopyCategory C ⥤ HomotopyCategory C :=
  ((OrdinaryStableHoAdditive.equivalence g) ^ n).functor

/-- Degree zero is the actual identity functor. -/
theorem shift_zero : shift g 0 = 𝟭 (HomotopyCategory C) := by unfold shift; rfl

/-- Degree one is the SAME actual framing ordinary suspension functor. -/
theorem shift_one : shift g 1 = Σ := by unfold shift; rfl

/-- Degree minus one is the SAME actual framing ordinary loop functor. -/
theorem shift_neg_one : shift g (-1) = Ω := by unfold shift; rfl

/-- Additivity of every integer shift is earned from the actual ordinary suspension and specified loop inverse. -/
theorem shift_additive (n : ℤ) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (shift g n).Additive := by
  let := OrdinaryStableHoPreadditive.preadditive g
  unfold shift
  let : (OrdinaryStableHoAdditive.equivalence g).functor.Additive :=
    OrdinaryStableHoAdditive.suspension_additive g
  exact Equivalence.IntegerSuccessor.additive (OrdinaryStableHoAdditive.equivalence g) n

/-- The original unitors, associators and counit give the full successor map at EVERY integer. -/
def successor (n : ℤ) : shift g n ⋙ Σ ≅ shift g (n + 1) := by
  unfold shift
  exact Equivalence.IntegerSuccessor.comparison (OrdinaryStableHoAdditive.equivalence g) n

/-- The negative-one successor retains the entire SAME original ordinary counit. -/
theorem successor_neg_one_hom (E : HomotopyCategory C) :
    HEq ((successor g (-1)).hom.app E) ((adjOrd).counit.app E) := by
  unfold successor shift
  rfl

/-- The SAME original unit and actual integer successor retain both inverse-adjoint comparison functions. -/
def inverseSuccessor (n : ℤ) : shift g n ≅ shift g (n + 1) ⋙ Ω := by
  unfold shift
  exact Equivalence.IntegerSuccessor.inverseComparison (OrdinaryStableHoAdditive.equivalence g) n

/-- Its entire function is the SAME original unit followed by the original loop-image successor. -/
theorem inverseSuccessor_hom (n : ℤ) (E : HomotopyCategory C) :
    (inverseSuccessor g n).hom.app E = (adjOrd).unit.app ((shift g n).obj E) ≫
      (Ω).map ((successor g n).hom.app E) := by
  unfold inverseSuccessor shift successor
  exact Equivalence.IntegerSuccessor.inverseComparison_hom (OrdinaryStableHoAdditive.equivalence g) n E

/-- The actual represented Hom type at EVERY integer degree. -/
abbrev hom (n : ℤ) (X E : HomotopyCategory C) := X ⟶ (shift g n).obj E

/-- Every represented integer Hom type has the SAME original constructed additive commutative group. -/
@[instance_reducible]
def homGroup (n : ℤ) (X E : HomotopyCategory C) : AddCommGroup (hom g n X E) :=
  OrdinaryStableHoPreadditive.homGroup g X ((shift g n).obj E)

/-- Every original Ho source arrow acts by its actual full precomposition at EVERY integer degree. -/
def sourceMap (n : ℤ) {X X' : HomotopyCategory C} (a : X ⟶ X') (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    hom g n X' E →+ hom g n X E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp _ a

/-- Every original Ho target arrow retains the full actual integer-shift map as an additive Hom map. -/
def targetMap (n : ℤ) (X : HomotopyCategory C) {E E' : HomotopyCategory C} (a : E ⟶ E') := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.rightComp X ((shift g n).map a)

/-- The original inverse-successor Iso and additive ordinary Hom functions give the actual integer step. -/
def homStep (n : ℤ) (X E : HomotopyCategory C) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let := OrdinaryStableHoAdditive.suspension_additive g
  exact stepFromAdjunction (adjOrd) X ((shift g n).obj E) ((shift g (n + 1)).obj E)
    ((inverseSuccessor g n).app E)

/-- The entire forward step function retains the SAME unit/successor word and original Hom inverse. -/
theorem homStep_apply (n : ℤ) (X E : HomotopyCategory C) (f : hom g n X E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homStep g n X E f = ((adjOrd).homEquiv X ((shift g (n + 1)).obj E)).symm
      (f ≫ (inverseSuccessor g n).hom.app E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  change ((adjOrd).homEquiv X ((shift g (n + 1)).obj E)).symm
    (𝟙 X ≫ f ≫ (inverseSuccessor g n).hom.app E) = _
  rw [Category.id_comp]

/-- The entire inverse step retains the SAME original Hom forward function and inverse comparison. -/
theorem homStep_symm_apply (n : ℤ) (X E : HomotopyCategory C)
    (f : (Σ).obj X ⟶ (shift g (n + 1)).obj E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (homStep g n X E).symm f = (adjOrd).homEquiv X ((shift g (n + 1)).obj E) f ≫
      (inverseSuccessor g n).inv.app E := by
  let := OrdinaryStableHoPreadditive.preadditive g
  change 𝟙 X ≫ (adjOrd).homEquiv X ((shift g (n + 1)).obj E) f ≫
    (inverseSuccessor g n).inv.app E = _
  rw [Category.id_comp]

/-- BOTH full original source functions preserve the actual additive integer Hom step. -/
theorem homStep_source (n : ℤ) {X X' : HomotopyCategory C} (a : X ⟶ X')
    (E : HomotopyCategory C) (f : hom g n X' E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homStep g n X E (a ≫ f) = (Σ).map a ≫ homStep g n X' E f := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [homStep_apply, homStep_apply, Category.assoc]
  exact (adjOrd).homEquiv_naturality_left_symm a _

/-- BOTH full original target functions preserve the actual additive integer Hom step. -/
theorem homStep_target (n : ℤ) (X : HomotopyCategory C) {E E' : HomotopyCategory C}
    (a : E ⟶ E') (f : hom g n X E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homStep g n X E' (f ≫ (shift g n).map a) =
      homStep g n X E f ≫ (shift g (n + 1)).map a := by
  let := OrdinaryStableHoPreadditive.preadditive g
  rw [homStep_apply, homStep_apply]
  apply ((adjOrd).homEquiv X ((shift g (n + 1)).obj E')).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  change (f ≫ (shift g n).map a) ≫ (inverseSuccessor g n).hom.app E' =
    (f ≫ (inverseSuccessor g n).hom.app E) ≫ (shift g (n + 1) ⋙ Ω).map a
  rw [Category.assoc, (inverseSuccessor g n).hom.naturality, ← Category.assoc]

end HomotopicalAlgebra.OrdinaryStableIntegerHom
