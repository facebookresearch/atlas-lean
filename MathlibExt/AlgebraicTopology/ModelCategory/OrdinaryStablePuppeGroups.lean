/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoPreadditive
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryPuppe
import Mathlib.CategoryTheory.Preadditive.Basic
import MathlibExt.CategoryTheory.Preadditive.ExactTargetIso

/-!
# Additive original Puppe restrictions and boundary maps

The original generated tower is unchanged. The earned original Ho Hom
groups make every restriction, source square and target composition an
additive homomorphism. The original image/null-kernel theorem becomes
group exactness at every stage, using the proved original null class = 0.
The complete boundary map and weak rotation comparison retain their
original functions as additive maps and equivalences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStablePuppeGroups

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

/-- The whole original stage Hom set into an arbitrary ordinary-Ho target. -/
abbrev term (n : ℕ) (F : Arrow C) (E : HomotopyCategory C) :=
  (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ n).obj F) ⟶ E

/-- Restriction is the original full step precomposition as an additive group homomorphism. -/
def restriction (n : ℕ) (F : Arrow C) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    term g Z hZ (n + 1) F E →+ term g Z hZ n F E := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E
    ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F))

/-- Every entire original Arrow square acts through its actual full term map as an additive homomorphism. -/
def sourceMap (n : ℕ) {F G : Arrow C} (a : F ⟶ G) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    term g Z hZ n G E →+ term g Z hZ n F E := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E
    ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.termFunctor g Z hZ n).map a))

/-- Every target Ho arrow acts by the original full postcomposition as an additive homomorphism. -/
def targetMap (n : ℕ) (F : Arrow C) {E E' : HomotopyCategory C} (a : E ⟶ E') :
    letI := OrdinaryStableHoPreadditive.preadditive g
    term g Z hZ n F E →+ term g Z hZ n F E' := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.rightComp
    ((toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ n).obj F)) a

/-- The complete additive restriction function is the unchanged original Puppe step. -/
theorem restriction_apply (n : ℕ) (F : Arrow C) (E : HomotopyCategory C)
    (h : term g Z hZ (n + 1) F E) :
    restriction g Z hZ n F E h = (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F) ≫ h := rfl

/-- Both original source-square legs preserve the complete additive restriction square. -/
theorem restriction_source (n : ℕ) {F G : Arrow C} (a : F ⟶ G) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (restriction g Z hZ n F E).comp (sourceMap g Z hZ (n + 1) a E) =
      (sourceMap g Z hZ n a E).comp (restriction g Z hZ n G E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  ext h
  change (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F) ≫
      ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.termFunctor g Z hZ (n + 1)).map a) ≫ h) =
    (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.termFunctor g Z hZ n).map a) ≫
      ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app G) ≫ h)
  rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f => (toHomotopyCategory C).map f ≫ h)
    ((GeneratedOrdinaryPuppe.step g Z hZ n).naturality a).symm

/-- Every original Ho target arrow preserves the full additive restriction square. -/
theorem restriction_target (n : ℕ) (F : Arrow C) {E E' : HomotopyCategory C} (a : E ⟶ E') :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (restriction g Z hZ n F E').comp (targetMap g Z hZ (n + 1) F a) =
      (targetMap g Z hZ n F a).comp (restriction g Z hZ n F E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  ext h
  change (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F) ≫ (h ≫ a) =
    ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F) ≫ h) ≫ a
  exact (Category.assoc _ _ _).symm

/-- At every original stage the actual group image is exactly the original zero kernel at a fibrant target. -/
theorem exact_at_fibrant (n : ℕ) (F : Arrow C) (E : C) [IsFibrant E]
    (h : term g Z hZ (n + 1) F ((toHomotopyCategory C).obj E)) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ t : term g Z hZ (n + 2) F ((toHomotopyCategory C).obj E),
      restriction g Z hZ (n + 1) F ((toHomotopyCategory C).obj E) t = h) ↔
      restriction g Z hZ n F ((toHomotopyCategory C).obj E) h = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  have ht := GeneratedOrdinaryPuppe.exact_at g Z hZ n F E h
  rw [OrdinaryStableHoPreadditive.nullHom_eq_zero g _ E] at ht
  simpa only [restriction_apply, GeneratedOrdinaryPuppe.restriction_apply] using ht

/-- The original R unit transports the SAME exact group sequence to every ordinary-Ho target. -/
theorem exact_at (n : ℕ) (F : Arrow C) (E : HomotopyCategory C) (h : term g Z hZ (n + 1) F E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ t : term g Z hZ (n + 2) F E, restriction g Z hZ (n + 1) F E t = h) ↔
      restriction g Z hZ n F E h = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let : (toHomotopyCategory C).EssSurj := Localization.essSurj (toHomotopyCategory C) (weakEquivalences C)
  let X : C := (toHomotopyCategory C).objPreimage E
  let r : (toHomotopyCategory C).obj X ⟶
      (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X) :=
    (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app X)
  let : IsIso r := Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
    (GeneratedFunctorialReplacements.unit_weak g X)
  let e : E ≅ (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X) :=
    ((toHomotopyCategory C).objObjPreimageIso E).symm ≪≫ asIso r
  let : IsFibrant ((GeneratedFunctorialReplacements.R g).obj X) :=
    GeneratedFunctorialReplacements.R_isFibrant g X
  have he : ∀ f : term g Z hZ (n + 1) F
      ((toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X)),
      (∃ t : term g Z hZ (n + 2) F
          ((toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X)),
        (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ (n + 1)).app F) ≫ t = f) ↔
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F) ≫ f = 0 := by
    intro f
    simpa only [restriction_apply] using
      exact_at_fibrant g Z hZ n F ((GeneratedFunctorialReplacements.R g).obj X) f
  have ht := Preadditive.exact_target_iso
    ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ n).app F))
    ((toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ (n + 1)).app F)) e he h
  simpa only [restriction_apply] using ht

/-- The original generated suspension object of the unchanged source term. -/
def suspendedSource (F : Arrow C) : C :=
  (GeneratedOrdinaryPuppe.termFunctor g Z hZ 0 ⋙ GeneratedOrdinaryPuppe.suspension g Z hZ).obj F

/-- The SAME original suspension source in Ho, kept opaque during Hom-instance elaboration. -/
@[irreducible]
def suspendedHoSource (F : Arrow C) : HomotopyCategory C :=
  (toHomotopyCategory C).obj (suspendedSource g Z hZ F)

/-- The SAME original Q-cofiber in Ho, kept opaque during Hom-instance elaboration. -/
@[irreducible]
def cofiberHo (F : Arrow C) : HomotopyCategory C :=
  (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).obj F)

/-- The full original boundary retains its actual source and codomain under that presentation. -/
def boundaryArrow (F : Arrow C) :
    cofiberHo g Z hZ F ⟶ suspendedHoSource g Z hZ F := by
  unfold suspendedHoSource cofiberHo
  exact (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.boundary g Z hZ).app F)

/-- The original boundary is a complete additive precomposition map on the same original suspension object. -/
def boundary (F : Arrow C) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E (boundaryArrow g Z hZ F)

/-- The additive original boundary retains its full unchanged source word. -/
theorem boundary_apply (F : Arrow C) (E : HomotopyCategory C)
    (h : suspendedHoSource g Z hZ F ⟶ E) :
    boundary g Z hZ F E h = boundaryArrow g Z hZ F ≫ h := rfl

end HomotopicalAlgebra.OrdinaryStablePuppeGroups
