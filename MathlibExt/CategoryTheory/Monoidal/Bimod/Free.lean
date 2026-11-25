/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Bimod
import all Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Adjunction.Basic
public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFree

/-!
# Free objects in the existing bimodule category

The free `(A,B)`-bimodule on `X` has the literal underlying object
`(A.X ⊗ X) ⊗ B.X`. Its two actions use the original multiplications,
and its free adjunction is with Mathlib's existing `Bimod.forget`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u

open CategoryTheory MonoidalCategory MonObj MonoidalOpposite
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The lawful left free action transported by the actual associator. -/
@[instance_reducible] def freeLeftStructure (A B : Mon C) (X : C) :
    ModObj A.X ((A.X ⊗ X) ⊗ B.X) := by
  let M : Mod C A.X := (Mod.free A.X).obj (X ⊗ B.X)
  letI : ModObj A.X (A.X ⊗ (X ⊗ B.X)) := M.mod
  let : IsMonHom (Iso.refl A.X).hom := by
    change IsMonHom (𝟙 A.X)
    infer_instance
  exact ModObj.ofIso (Iso.refl A.X) (α_ A.X X B.X).symm

/-- The lawful right action on the literal free tensor triple. -/
@[instance_reducible] def freeRightStructure (A B : Mon C) (X : C) :
    ModObj (mop B.X) ((A.X ⊗ X) ⊗ B.X) :=
  (RightModuleFree.freeObject B.X (A.X ⊗ X)).mod

/-- The transported free left action is the original multiplication and associators. -/
theorem freeLeftStructure_smul (A B : Mon C) (X : C) :
    (freeLeftStructure A B X).smul =
      (α_ A.X (A.X ⊗ X) B.X).inv ≫
        ((α_ A.X A.X X).inv ≫ (μ[A.X] ▷ X)) ▷ B.X := by
  change (𝟙 A.X ⊗ₘ (α_ A.X X B.X).hom) ≫ ((α_ A.X A.X (X ⊗ B.X)).inv ≫
    μ[A.X] ▷ (X ⊗ B.X)) ≫ (α_ A.X X B.X).inv = _
  simp only [id_tensorHom, Category.assoc]
  rw [associator_inv_naturality_left]
  have h : (A.X ◁ (α_ A.X X B.X).hom) ≫ (α_ A.X A.X (X ⊗ B.X)).inv ≫
      (α_ (A.X ⊗ A.X) X B.X).inv =
      (α_ A.X (A.X ⊗ X) B.X).inv ≫ ((α_ A.X A.X X).inv ▷ B.X) := by monoidal
  slice_lhs 1 3 => rw [h]
  simp only [Category.assoc]
  rw [← comp_whiskerRight]

/-- The existing free right action is the original coefficient multiplication. -/
theorem freeRightStructure_smul (A B : Mon C) (X : C) :
    (freeRightStructure A B X).smul =
      (α_ (A.X ⊗ X) B.X B.X).hom ≫ (A.X ⊗ X) ◁ μ[B.X] := by
  exact RightModuleFree.freeObject_action B.X (A.X ⊗ X)

/-- Left action extension commutes with the independent original right coefficient contraction. -/
theorem tensorAction_commute (P Q R : C) (a : P ⊗ Q ⟶ Q) (b : R ⊗ R ⟶ R) :
    ((α_ P Q R).inv ≫ a ▷ R) ▷ R ≫ (α_ Q R R).hom ≫ Q ◁ b =
      (α_ P (Q ⊗ R) R).hom ≫ P ◁ ((α_ Q R R).hom ≫ Q ◁ b) ≫
        (α_ P Q R).inv ≫ a ▷ R := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange]
  rw [associator_inv_naturality_right_assoc]
  have h : ((α_ P Q R).inv ▷ R) ≫ (α_ (P ⊗ Q) R R).hom =
      (α_ P (Q ⊗ R) R).hom ≫ (P ◁ (α_ Q R R).hom) ≫ (α_ P Q (R ⊗ R)).inv := by monoidal
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc]

/-- The free bimodule, retaining the literal original source tensor and both original actions. -/
@[reducible] def freeObject (A B : Mon C) (X : C) : Bimod A B := by
  let Y := (A.X ⊗ X) ⊗ B.X
  letI : ModObj A.X Y := freeLeftStructure A B X
  letI : ModObj (mop B.X) Y := freeRightStructure A B X
  refine
    { X := Y
      actLeft := γ[A.X, Y]
      actRight := γ[mop B.X, Y]
      one_actLeft := ModObj.one_smul_self A.X Y
      left_assoc := ModObj.mul_smul_self A.X Y
      actRight_one := ModObj.one_smul (M := mop B.X) Y
      right_assoc := ModObj.mul_smul (M := mop B.X) Y
      middle_assoc := ?_ }
  change (freeLeftStructure A B X).smul ▷ B.X ≫ (freeRightStructure A B X).smul =
    (α_ A.X Y B.X).hom ≫ A.X ◁ (freeRightStructure A B X).smul ≫
      (freeLeftStructure A B X).smul
  rw [freeLeftStructure_smul, freeRightStructure_smul]
  exact tensorAction_commute A.X (A.X ⊗ X) B.X ((α_ A.X A.X X).inv ≫ μ[A.X] ▷ X) μ[B.X]

/-- The actual free carrier is the original tensor triple. -/
theorem freeObject_X (A B : Mon C) (X : C) : (freeObject A B X).X = (A.X ⊗ X) ⊗ B.X := rfl

/-- The complete original left multiplication action on the free tensor triple. -/
theorem freeObject_actLeft (A B : Mon C) (X : C) :
    (freeObject A B X).actLeft = (α_ A.X (A.X ⊗ X) B.X).inv ≫
      ((α_ A.X A.X X).inv ≫ μ[A.X] ▷ X) ▷ B.X :=
  freeLeftStructure_smul A B X

/-- The complete original right multiplication action on the same triple. -/
theorem freeObject_actRight (A B : Mon C) (X : C) :
    (freeObject A B X).actRight = (α_ (A.X ⊗ X) B.X B.X).hom ≫ (A.X ⊗ X) ◁ μ[B.X] :=
  freeRightStructure_smul A B X

/-- A source arrow gives its literal left-and-right tensor map between free bimodules. -/
def freeMap (A B : Mon C) {X Y : C} (f : X ⟶ Y) : freeObject A B X ⟶ freeObject A B Y where
  hom := (A.X ◁ f) ▷ B.X
  left_act_hom := by
    change (freeObject A B X).actLeft ≫ (A.X ◁ f) ▷ B.X =
      A.X ◁ ((A.X ◁ f) ▷ B.X) ≫ (freeObject A B Y).actLeft
    rw [freeObject_actLeft A B X, freeObject_actLeft A B Y]
    have h : ((α_ A.X A.X X).inv ≫ μ[A.X] ▷ X) ≫ (A.X ◁ f) =
        (A.X ◁ (A.X ◁ f)) ≫ ((α_ A.X A.X Y).inv ≫ μ[A.X] ▷ Y) := by
      simp only [Category.assoc]
      rw [← whisker_exchange, associator_inv_naturality_right_assoc]
    simp only [Category.assoc]
    rw [← comp_whiskerRight, h, comp_whiskerRight]
    rw [associator_inv_naturality_middle_assoc]
  right_act_hom := by
    change (freeObject A B X).actRight ≫ (A.X ◁ f) ▷ B.X =
      ((A.X ◁ f) ▷ B.X) ▷ B.X ≫ (freeObject A B Y).actRight
    rw [freeObject_actRight A B X, freeObject_actRight A B Y]
    simp only [Category.assoc]
    rw [whisker_exchange, associator_naturality_left_assoc]

/-- The actual free functor into Mathlib's existing bimodule category. -/
def free (A B : Mon C) : C ⥤ Bimod A B where
  obj := freeObject A B
  map := freeMap A B
  map_id X := by
    apply hom_ext
    change (A.X ◁ 𝟙 X) ▷ B.X = 𝟙 ((A.X ⊗ X) ⊗ B.X)
    rw [whiskerLeft_id, id_whiskerRight]
  map_comp f g := by
    apply hom_ext
    change (A.X ◁ (f ≫ g)) ▷ B.X = (A.X ◁ f) ▷ B.X ≫ (A.X ◁ g) ▷ B.X
    rw [whiskerLeft_comp, comp_whiskerRight]

/-- The original whole underlying map of the free functor. -/
theorem free_map_hom (A B : Mon C) {X Y : C} (f : X ⟶ Y) :
    ((free A B).map f).hom = (A.X ◁ f) ▷ B.X := rfl

/-- The actual original free generator inserts the two coefficient units. -/
def freeGenerator (A B : Mon C) (X : C) : X ⟶ (freeObject A B X).X :=
  (λ_ X).inv ≫ η[A.X] ▷ X ≫ (ρ_ (A.X ⊗ X)).inv ≫ (A.X ⊗ X) ◁ η[B.X]

/-- Extend a source map using the existing target's two commuting actions. -/
def extend (A B : Mon C) {X : C} (M : Bimod A B) (f : X ⟶ M.X) : freeObject A B X ⟶ M where
  hom := ((A.X ◁ f) ≫ M.actLeft) ▷ B.X ≫ M.actRight
  left_act_hom := by
    let a := (A.X ◁ f) ≫ M.actLeft
    have ha : ((α_ A.X A.X X).inv ≫ μ[A.X] ▷ X) ≫ a =
        (A.X ◁ a) ≫ M.actLeft := by
      dsimp only [a]
      simp only [Category.assoc, whiskerLeft_comp]
      rw [← whisker_exchange_assoc, M.left_assoc,
        associator_naturality_right_assoc, Iso.inv_hom_id_assoc]
    change (freeObject A B X).actLeft ≫ a ▷ B.X ≫ M.actRight =
      A.X ◁ (a ▷ B.X ≫ M.actRight) ≫ M.actLeft
    rw [freeObject_actLeft]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, ha, comp_whiskerRight]
    simp only [Category.assoc]
    rw [← associator_inv_naturality_middle_assoc, M.middle_assoc,
      Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc]
  right_act_hom := by
    let a := (A.X ◁ f) ≫ M.actLeft
    change (freeObject A B X).actRight ≫ a ▷ B.X ≫ M.actRight =
      (a ▷ B.X ≫ M.actRight) ▷ B.X ≫ M.actRight
    rw [freeObject_actRight]
    simp only [comp_whiskerRight, Category.assoc]
    rw [whisker_exchange_assoc, ← associator_naturality_left_assoc,
      M.right_assoc, Iso.hom_inv_id_assoc]

/-- The entire underlying arrow of the free extension is the two original target actions. -/
theorem extend_hom (A B : Mon C) {X : C} (M : Bimod A B) (f : X ⟶ M.X) :
    (extend A B M f).hom = ((A.X ◁ f) ≫ M.actLeft) ▷ B.X ≫ M.actRight := rfl

/-- Extending and then restricting to the original generator recovers the whole source map. -/
theorem freeGenerator_extend (A B : Mon C) {X : C} (M : Bimod A B) (f : X ⟶ M.X) :
    freeGenerator A B X ≫ (extend A B M f).hom = f := by
  rw [extend_hom]
  simp only [freeGenerator, Category.assoc]
  rw [whisker_exchange_assoc, M.actRight_one, rightUnitor_naturality, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc, M.one_actLeft, leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- Extending the original generator inside its free bimodule is the entire identity map. -/
theorem extend_freeGenerator_id (A B : Mon C) (X : C) :
    extend A B (freeObject A B X) (freeGenerator A B X) = 𝟙 (freeObject A B X) := by
  apply hom_ext
  let P := A.X ⊗ X
  let l : X ⟶ P := (λ_ X).inv ≫ η[A.X] ▷ X
  let r (Q : C) : Q ⟶ Q ⊗ B.X := (ρ_ Q).inv ≫ Q ◁ η[B.X]
  let a : A.X ⊗ P ⟶ P := (α_ A.X A.X X).inv ≫ μ[A.X] ▷ X
  have hl : (A.X ◁ l) ≫ a = 𝟙 P := (Monad.tensorMonad A.X).right_unit X
  have hr : r P ▷ B.X ≫ ((α_ P B.X B.X).hom ≫ P ◁ μ[B.X]) = 𝟙 (P ⊗ B.X) := by
    have hu := congrArg Quiver.Hom.unmop ((Monad.tensorMonad (mop B.X)).right_unit (mop P))
    exact hu
  have hline : (A.X ◁ r P) ≫ (α_ A.X P B.X).inv = r (A.X ⊗ P) := by
    dsimp only [r]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_right, ← rightUnitor_tensor_inv_assoc]
  have hnat : r (A.X ⊗ P) ≫ a ▷ B.X = a ≫ r P := by
    dsimp only [r]
    simp only [Category.assoc]
    rw [whisker_exchange, rightUnitor_inv_naturality_assoc]
  have hla : (A.X ◁ r P) ≫ ((α_ A.X P B.X).inv ≫ a ▷ B.X) = a ≫ r P := by
    rw [← Category.assoc, hline, hnat]
  have hlr : (A.X ◁ l) ≫ a ≫ r P = r P := by
    rw [← Category.assoc, hl, Category.id_comp]
  have hg : freeGenerator A B X = l ≫ r P := by
    simp only [freeGenerator, l, r, P, Category.assoc]
  rw [extend_hom, hg]
  change ((A.X ◁ (l ≫ r P)) ≫ (freeObject A B X).actLeft) ▷ B.X ≫
    (freeObject A B X).actRight = 𝟙 (P ⊗ B.X)
  rw [freeObject_actLeft, freeObject_actRight]
  change ((A.X ◁ (l ≫ r P)) ≫ ((α_ A.X P B.X).inv ≫ a ▷ B.X)) ▷ B.X ≫
    ((α_ P B.X B.X).hom ≫ P ◁ μ[B.X]) = 𝟙 (P ⊗ B.X)
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hla, hlr]
  exact hr

/-- Every original bimodule map is determined by its complete generator restriction. -/
theorem extend_freeGenerator (A B : Mon C) {X : C} {M : Bimod A B}
    (q : freeObject A B X ⟶ M) :
    extend A B M (freeGenerator A B X ≫ q.hom) = q := by
  apply hom_ext
  rw [extend_hom, whiskerLeft_comp, Category.assoc, ← q.left_act_hom]
  rw [← Category.assoc, comp_whiskerRight, Category.assoc, ← q.right_act_hom]
  have h : ((A.X ◁ freeGenerator A B X) ≫ (freeObject A B X).actLeft) ▷ B.X ≫
      (freeObject A B X).actRight = 𝟙 (freeObject A B X).X :=
    congrArg Hom.hom (extend_freeGenerator_id A B X)
  rw [← Category.assoc, h, Category.id_comp]

/-- The full free bimodule Hom equivalence, on the original source and target maps. -/
def freeHomEquiv (A B : Mon C) (X : C) (M : Bimod A B) :
    (freeObject A B X ⟶ M) ≃ (X ⟶ M.X) where
  toFun q := freeGenerator A B X ≫ q.hom
  invFun f := extend A B M f
  left_inv := extend_freeGenerator A B
  right_inv := freeGenerator_extend A B M

/-- The full free adjunction with the original bimodule forgetful functor. -/
def freeForgetAdjunction (A B : Mon C) : free A B ⊣ forget (B := B) A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeHomEquiv A B
      homEquiv_naturality_left_symm := fun {X' X M} f g => by
        apply hom_ext
        change ((A.X ◁ (f ≫ g)) ≫ M.actLeft) ▷ B.X ≫ M.actRight =
          (A.X ◁ f) ▷ B.X ≫ ((A.X ◁ g) ≫ M.actLeft) ▷ B.X ≫ M.actRight
        simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      homEquiv_naturality_right := fun {X M N} q f => by
        change freeGenerator A B X ≫ q.hom ≫ f.hom =
          (freeGenerator A B X ≫ q.hom) ≫ f.hom
        exact (Category.assoc _ _ _).symm }

/-- The whole selected Hom equivalence is the original generator-and-action equivalence. -/
theorem freeForgetAdjunction_homEquiv (A B : Mon C) :
    (freeForgetAdjunction A B).homEquiv = freeHomEquiv A B := by
  unfold freeForgetAdjunction
  exact Adjunction.mkOfHomEquiv_homEquiv _

/-- Every selected free-adjunction unit component is the original two-unit insertion. -/
theorem freeForgetAdjunction_unit_app (A B : Mon C) (X : C) :
    (freeForgetAdjunction A B).unit.app X = freeGenerator A B X := by
  change freeGenerator A B X ≫ 𝟙 (freeObject A B X).X = freeGenerator A B X
  exact Category.comp_id _

/-- Every selected free-adjunction counit is exactly the original two target actions. -/
theorem freeForgetAdjunction_counit_app_hom (A B : Mon C) (M : Bimod A B) :
    ((freeForgetAdjunction A B).counit.app M).hom = M.actLeft ▷ B.X ≫ M.actRight := by
  change ((A.X ◁ 𝟙 M.X) ≫ M.actLeft) ▷ B.X ≫ M.actRight = M.actLeft ▷ B.X ≫ M.actRight
  rw [whiskerLeft_id, Category.id_comp]

/-- The original free bimodule functor is a genuine left adjoint. -/
instance freeIsLeftAdjoint (A B : Mon C) : (free A B).IsLeftAdjoint :=
  (freeForgetAdjunction A B).isLeftAdjoint

/-- The original bimodule forgetful functor is a genuine right adjoint. -/
instance forgetIsRightAdjoint (A B : Mon C) : (forget (B := B) A).IsRightAdjoint :=
  (freeForgetAdjunction A B).isRightAdjoint

end Bimod
