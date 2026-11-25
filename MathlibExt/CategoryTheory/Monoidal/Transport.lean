/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-!
# Formulas and symmetric data for transported monoidal categories

The tensor objects, maps, unit, associator, unitors, and braiding retain
the complete functor, inverse functor, unit, and counit of the source equivalence.
The source tensor comparison keeps its full naturality and braiding equations.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal.Transport

section SymmetricData

universe uC vC uD vD
open CategoryTheory

/-- The entire target symmetric structure type is written against the actual tensor data. -/
def SymmetricType {D : Type uD} [Category.{vD} D] (tensor : MonoidalCategory D) : Type _ :=
  letI := tensor
  SymmetricCategory D

/-- The complete original source symmetric transport, at symbolic source/equivalence data. -/
def sourceSymmetric {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [SymmetricCategory C] {D : Type uD} [Category.{vD} D] (E : C ≌ D) :
    SymmetricType (Monoidal.transport E) :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported E))

/-- Move the complete original symmetric dictionary by the proved entire tensor equality. -/
def moveSymmetric {D : Type uD} [Category.{vD} D]
    (native original : MonoidalCategory D) (h : native = original)
    (S : SymmetricType original) : SymmetricType native := by
  cases h
  exact S




end SymmetricData

namespace TensorLaws

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [MonoidalCategory C]

/-- The entire original tensor-object formula, with both original functor objects. -/
def ObjectFormula (e : C ≌ D) (native : MonoidalCategory D) (X Y : D) : Prop :=
  letI := native
  X ⊗ Y = e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)

/-- The entire original tensor-map Eq at the source-computed transported dictionary. -/
def MapFormula (e : C ≌ D) {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  f ⊗ₘ g = e.functor.map (e.inverse.map f ⊗ₘ e.inverse.map g)

/-- The complete original left tensor functor, including every original functor map. -/
def LeftFormula (e : C ≌ D) (native : MonoidalCategory D) (X : D) : Prop :=
  letI := native
  tensorLeft X = e.inverse ⋙ tensorLeft (e.inverse.obj X) ⋙ e.functor

/-- The complete original right tensor functor at the same original source equivalence. -/
def RightFormula (e : C ≌ D) (native : MonoidalCategory D) (X : D) : Prop :=
  letI := native
  tensorRight X = e.inverse ⋙ tensorRight (e.inverse.obj X) ⋙ e.functor

/-- The original entire source-unit object retains the actual forward functor. -/
def UnitFormula (e : C ≌ D) (native : MonoidalCategory D) : Prop :=
  letI := native
  (𝟙_ D) = e.functor.obj (𝟙_ C)

/-- The generic original transport computes its complete tensor object. -/
theorem object_original (e : C ≌ D) (X Y : D) :
    ObjectFormula e (Monoidal.transport e) X Y := rfl

/-- The generic original transport computes both full tensor input maps. -/
theorem map_original (e : C ≌ D) {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    MapFormula e f g := rfl

/-- The generic source tensor preserves the entire left-oriented original functor word. -/
theorem left_original (e : C ≌ D) (X : D) :
    LeftFormula e (Monoidal.transport e) X := rfl

/-- The generic source tensor preserves the entire right-oriented original functor word. -/
theorem right_original (e : C ≌ D) (X : D) :
    RightFormula e (Monoidal.transport e) X := rfl

/-- The generic transport retains the entire original source-unit object. -/
theorem unit_original (e : C ≌ D) : UnitFormula e (Monoidal.transport e) := rfl

/-- An equality of whole dictionaries transports the same complete tensor-object formula. -/
theorem object_of_eq (e : C ≌ D) (native : MonoidalCategory D)
    (h : native = Monoidal.transport e) (X Y : D) : ObjectFormula e native X Y := by
  cases h
  exact object_original e X Y

/-- The complete left functor word follows from the same whole dictionary equality. -/
theorem left_of_eq (e : C ≌ D) (native : MonoidalCategory D)
    (h : native = Monoidal.transport e) (X : D) : LeftFormula e native X := by
  cases h
  exact left_original e X

/-- The complete right functor word follows from that same whole dictionary equality. -/
theorem right_of_eq (e : C ≌ D) (native : MonoidalCategory D)
    (h : native = Monoidal.transport e) (X : D) : RightFormula e native X := by
  cases h
  exact right_original e X

/-- The original source-unit object is transported by the same unconditional equality. -/
theorem unit_of_eq (e : C ≌ D) (native : MonoidalCategory D)
    (h : native = Monoidal.transport e) : UnitFormula e native := by
  cases h
  exact unit_original e

end TensorLaws

namespace SourceTensorIso

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D]

/-- The complete original source tensor Iso type, for every actual target tensor dictionary. -/
def IsoFamily (E : C ≌ D) (tensor : MonoidalCategory D) : Type _ :=
  letI := tensor
  ∀ (X Y : D), E.inverse.obj X ⊗ E.inverse.obj Y ≅ E.inverse.obj (X ⊗ Y)

/-- The exact original source unit supplies the whole Iso family under the original transport. -/
def originalIso (E : C ≌ D) : IsoFamily E (Monoidal.transport E) := by
  letI : MonoidalCategory D := Monoidal.transport E
  intro X Y
  exact E.unitIso.app (E.inverse.obj X ⊗ E.inverse.obj Y)

/-- Move the same full original unit Iso family along the actual entire dictionary equality. -/
def isoOfEq (E : C ≌ D) (tensor : MonoidalCategory D)
    (h : tensor = Monoidal.transport E) : IsoFamily E tensor := by
  cases h
  exact originalIso E

/-- The whole original homogeneous f/g Eq, with all four objects and both inverse-functor maps. -/
def Natural (E : C ≌ D) (tensor : MonoidalCategory D)
    (comparison : IsoFamily E tensor) : Prop :=
  letI := tensor
  ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
    (E.inverse.map f ⊗ₘ E.inverse.map g) ≫ (comparison X' Y').hom =
      (comparison X Y).hom ≫ E.inverse.map (f ⊗ₘ g)

/-- The actual original unit naturality gives the complete original two-map equation. -/
theorem originalNatural (E : C ≌ D) :
    Natural E (Monoidal.transport E) (originalIso E) := by
  let : MonoidalCategory D := Monoidal.transport E
  intro X X' Y Y' f g
  exact E.unitIso.hom.naturality (E.inverse.map f ⊗ₘ E.inverse.map g)

/--
The whole homogeneous original naturality word is kept by the same actual dictionary equality.
-/
theorem natural_of_eq (E : C ≌ D) (tensor : MonoidalCategory D)
    (h : tensor = Monoidal.transport E) :
    Natural E tensor (isoOfEq E tensor h) := by
  cases h
  exact originalNatural E

end SourceTensorIso

namespace SourceCoherence

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [MonoidalCategory C]

/-- The original full left-whisker map at the source-computed transported tensor. -/
def WhiskerLeftFormula (e : C ≌ D) (X : D) {Y Z : D} (f : Y ⟶ Z) : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  X ◁ f = e.functor.map (e.inverse.obj X ◁ e.inverse.map f)

/-- The original full right-whisker map at that same computed transported tensor. -/
def WhiskerRightFormula (e : C ≌ D) {X Y : D} (f : X ⟶ Y) (Z : D) : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  f ▷ Z = e.functor.map (e.inverse.map f ▷ e.inverse.obj Z)

/-- The full original associator retains both intermediate source-unit comparisons. -/
def AssociatorFormula (e : C ≌ D) (X Y Z : D) : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  (α_ X Y Z) = e.functor.mapIso
    (whiskerRightIso
      (e.unitIso.app (e.inverse.obj X ⊗ e.inverse.obj Y)).symm (e.inverse.obj Z) ≪≫
      (α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z)) ≪≫
      whiskerLeftIso (e.inverse.obj X)
        (e.unitIso.app (e.inverse.obj Y ⊗ e.inverse.obj Z)))

/-- The full original left unitor keeps the inverse source-unit comparison and actual counit. -/
def LeftUnitorFormula (e : C ≌ D) (X : D) : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  (λ_ X) = e.functor.mapIso
    (whiskerRightIso (e.unitIso.app (𝟙_ C)).symm (e.inverse.obj X) ≪≫
      (λ_ (e.inverse.obj X))) ≪≫ e.counitIso.app X

/-- The full original right unitor keeps the other inverse unit comparison and the same counit. -/
def RightUnitorFormula (e : C ≌ D) (X : D) : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  (ρ_ X) = e.functor.mapIso
    (whiskerLeftIso (e.inverse.obj X) (e.unitIso.app (𝟙_ C)).symm ≪≫
      (ρ_ (e.inverse.obj X))) ≪≫ e.counitIso.app X

/-- Original transport computes every complete left source-whisker map. -/
theorem whiskerLeft_original (e : C ≌ D) (X : D) {Y Z : D} (f : Y ⟶ Z) :
    WhiskerLeftFormula e X f := rfl

/-- Original transport computes every complete right source-whisker map. -/
theorem whiskerRight_original (e : C ≌ D) {X Y : D} (f : X ⟶ Y) (Z : D) :
    WhiskerRightFormula e f Z := rfl

/-- The actual original transported associator has the full two-unit source word. -/
theorem associator_original (e : C ≌ D) (X Y Z : D) :
    AssociatorFormula e X Y Z := rfl

/-- The actual original transported left unitor retains its complete source/counit word. -/
theorem leftUnitor_original (e : C ≌ D) (X : D) : LeftUnitorFormula e X := rfl

/-- The actual original transported right unitor retains its complete source/counit word. -/
theorem rightUnitor_original (e : C ≌ D) (X : D) : RightUnitorFormula e X := rfl

variable [SymmetricCategory C]

/-- The complete computed native braid is the original entire source braid under reconstruction. -/
def BraidingFormula (e : C ≌ D) (X Y : D) : Prop :=
  letI : MonoidalCategory D := Monoidal.transport e
  letI : SymmetricCategory D := sourceSymmetric e
  (β_ X Y) = e.functor.mapIso (β_ (e.inverse.obj X) (e.inverse.obj Y))

/-- The entire original symmetric transport computes the same complete source braid. -/
theorem braiding_original (e : C ≌ D) (X Y : D) : BraidingFormula e X Y := rfl

end SourceCoherence

namespace SourceTensorIso
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type uD} [Category.{vD} D]

/-- The complete original source-unit braid equation at the computed native symmetry. -/
def Braiding (E : C ≌ D) (tensor : MonoidalCategory D)
    (h : tensor = Monoidal.transport E) : Prop :=
  letI := tensor
  letI : SymmetricCategory D := moveSymmetric tensor
    (Monoidal.transport E) h (sourceSymmetric E)
  ∀ (X Y : D),
    (isoOfEq E tensor h X Y).hom ≫ E.inverse.map (β_ X Y).hom =
      (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom ≫ (isoOfEq E tensor h Y X).hom

/-- Naturality of the original equivalence unit retains the complete source braiding. -/
theorem braiding_of_eq (E : C ≌ D) (tensor : MonoidalCategory D)
    (h : tensor = Monoidal.transport E) : Braiding E tensor h := by
  cases h
  let : MonoidalCategory D := Monoidal.transport E
  let : SymmetricCategory D := sourceSymmetric E
  intro X Y
  exact (E.unitIso.hom.naturality (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom).symm

end SourceTensorIso

namespace SourceTensorIso
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type uD} [Category.{vD} D]

/-- The whole original braid at an explicitly selected symmetry and complete Iso family. -/
def BraidingFor (E : C ≌ D) (tensor : MonoidalCategory D)
    (symmetry : SymmetricType tensor)
    (comparison : IsoFamily E tensor) : Prop :=
  letI := tensor
  letI : SymmetricCategory D := symmetry
  ∀ (X Y : D),
    (comparison X Y).hom ≫ E.inverse.map (β_ X Y).hom =
      (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom ≫ (comparison Y X).hom

/-- The original whole dictionaries supply the complete braid at their proved equal selections. -/
theorem braidingFor_of_eq (E : C ≌ D) (tensor : MonoidalCategory D)
    (h : tensor = Monoidal.transport E)
    (symmetry : SymmetricType tensor)
    (symmetry_eq : symmetry = moveSymmetric tensor
      (Monoidal.transport E) h (sourceSymmetric E))
    (comparison : IsoFamily E tensor)
    (comparison_eq : comparison = isoOfEq E tensor h) :
    BraidingFor E tensor symmetry comparison := by
  cases symmetry_eq
  cases comparison_eq
  exact braiding_of_eq E tensor h

/--
The complete source-unit braid retains every source postcomposition and both full dictionaries.
-/
def BraidingAssocFor (E : C ≌ D) (tensor : MonoidalCategory D)
    (symmetry : SymmetricType tensor)
    (comparison : IsoFamily E tensor) : Prop :=
  letI := tensor
  letI : SymmetricCategory D := symmetry
  ∀ (X Y : D) {Z : C} (k : E.inverse.obj (Y ⊗ X) ⟶ Z),
    (comparison X Y).hom ≫ E.inverse.map (β_ X Y).hom ≫ k =
      (β_ (E.inverse.obj X) (E.inverse.obj Y)).hom ≫ (comparison Y X).hom ≫ k

/-- The complete original braid supplier preserves every map under arbitrary postcomposition. -/
theorem braidingAssocFor_of_eq (E : C ≌ D) (tensor : MonoidalCategory D)
    (h : tensor = Monoidal.transport E)
    (symmetry : SymmetricType tensor)
    (symmetry_eq : symmetry = moveSymmetric tensor
      (Monoidal.transport E) h (sourceSymmetric E))
    (comparison : IsoFamily E tensor)
    (comparison_eq : comparison = isoOfEq E tensor h) :
    BraidingAssocFor E tensor symmetry comparison := by
  let := tensor
  let : SymmetricCategory D := symmetry
  intro X Y Z k
  exact (Category.assoc _ _ k).symm.trans
    ((congrArg (fun t => t ≫ k)
      (braidingFor_of_eq E tensor h symmetry symmetry_eq comparison comparison_eq X Y)).trans
        (Category.assoc _ _ k))

end SourceTensorIso

end CategoryTheory.Monoidal.Transport
