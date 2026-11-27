/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Adjunction.FunctionUnit
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Public clients of selected units for arbitrary categories

These clients import only the generic adjunction API. They retain the given
adjunctions, source transformations and independent input and target objects.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.FunctionUnitAdjunction

namespace FunctionUnitClient

universe u v
variable {C : Type u} [Category.{v} C]

example {F G : C ⥤ C} (adj : F ⊣ G) (unitIso : G ≅ 𝟭 C) (X : C) :
    (adj.homEquiv X X) ((leftUnitIso adj unitIso).hom.app X) = unitIso.inv.app X :=
  unitInverse_adjoint adj unitIso X

example {F G : C ⥤ C} (adj : F ⊣ G) (unitIso : G ≅ 𝟭 C) (X : C) :
    (adj.homEquiv X X).symm (unitIso.inv.app X) = (leftUnitIso adj unitIso).hom.app X :=
  unitInverse_uncurried adj unitIso X

variable {L : C ⥤ (C ⥤ C)} {R : Cᵒᵖ ⥤ (C ⥤ C)} (adj : L ⊣₂ R)

example {S T : C} (f : S ⟶ T) {X Y : C} (g : (L.obj T).obj X ⟶ Y) :
    ((adj.adj S).homEquiv X Y) ((L.map f).app X ≫ g) =
      ((adj.adj T).homEquiv X Y) g ≫ (R.map f.op).app Y :=
  sourcePre_adjoint_of_whole_eq adj f (L.obj S) (L.obj T) (R.obj (.op S)) (R.obj (.op T))
    rfl rfl rfl rfl (adj.adj S) (adj.adj T) (HEq.refl _) (HEq.refl _)
    (L.map f) (R.map f.op) (HEq.refl _) (HEq.refl _) g

example {S T : C} (f : S ⟶ T) (unitIso : R.obj (.op T) ≅ 𝟭 C) (X : C) :
    ((adj.adj S).homEquiv X X)
      ((L.map f).app X ≫ (leftUnitIso (adj.adj T) unitIso).hom.app X) =
      unitIso.inv.app X ≫ (R.map f.op).app X :=
  sourcePre_unit_adjoint adj f unitIso X

example {S T : C} (f : S ⟶ T) (unitIso : R.obj (.op T) ≅ 𝟭 C) (X : C) :
    ((adj.adj S).homEquiv X X).symm (unitIso.inv.app X ≫ (R.map f.op).app X) =
      (L.map f).app X ≫ (leftUnitIso (adj.adj T) unitIso).hom.app X :=
  sourcePre_unit_uncurried adj f unitIso X

example {F G : C ⥤ C} (a : F ⊣ G) (s : F ⟶ 𝟭 C) (η : 𝟭 C ⟶ G)
    (h : ∀ X : C, (a.homEquiv X X) (s.app X) = η.app X) {P X : C} (f : P ⟶ X) :
    (a.homEquiv P X) (s.app P ≫ f) = η.app P ≫ G.map f :=
  sourceAdjunct_target_of_mate a s η h f

example {F G : C ⥤ C} (a : F ⊣ G) (s : F ⟶ 𝟭 C) (η : 𝟭 C ⟶ G)
    (h : ∀ X : C, (a.homEquiv X X) (s.app X) = η.app X) {P X : C} (f : P ⟶ X) :
    (a.homEquiv P X) (F.map f ≫ s.app X) = f ≫ η.app X :=
  sourceAdjunct_input_of_mate a s η h f

section IndependentCategories

universe uP vP uC vC uD vD
variable {P : Type uP} [Category.{vP} P]
  {A : Type uC} [Category.{vC} A] {B : Type uD} [Category.{vD} B]

-- The parameter and both component categories retain independent object and Hom universes.
example {L : P ⥤ (A ⥤ B)} {R : Pᵒᵖ ⥤ (B ⥤ A)} (a : L ⊣₂ R)
    {S T : P} (f : S ⟶ T) {X : A} {Y : B} (g : (L.obj T).obj X ⟶ Y) :
    ((a.adj S).homEquiv X Y) ((L.map f).app X ≫ g) =
      ((a.adj T).homEquiv X Y) g ≫ (R.map f.op).app Y :=
  sourcePre_adjoint_of_whole_eq a f (L.obj S) (L.obj T) (R.obj (.op S)) (R.obj (.op T))
    rfl rfl rfl rfl (a.adj S) (a.adj T) (HEq.refl _) (HEq.refl _)
    (L.map f) (R.map f.op) (HEq.refl _) (HEq.refl _) g

-- Complete, independently named endpoint functors and maps are transported before components.
example {L : P ⥤ (A ⥤ B)} {R : Pᵒᵖ ⥤ (B ⥤ A)} (a : L ⊣₂ R)
    {S T : P} (f : S ⟶ T) (FS FT : A ⥤ B) (GS GT : B ⥤ A)
    (hFS : L.obj S = FS) (hFT : L.obj T = FT)
    (hGS : R.obj (.op S) = GS) (hGT : R.obj (.op T) = GT)
    (adjS : FS ⊣ GS) (adjT : FT ⊣ GT)
    (hAdjS : HEq (a.adj S) adjS) (hAdjT : HEq (a.adj T) adjT)
    (sourceMap : FS ⟶ FT) (preMap : GT ⟶ GS)
    (hMap : HEq (L.map f) sourceMap) (hPre : HEq (R.map f.op) preMap)
    {X : A} {Y : B} (g : FT.obj X ⟶ Y) :
    (adjS.homEquiv X Y) (sourceMap.app X ≫ g) =
      (adjT.homEquiv X Y) g ≫ preMap.app Y :=
  sourcePre_adjoint_of_whole_eq a f FS FT GS GT hFS hFT hGS hGT
    adjS adjT hAdjS hAdjT sourceMap preMap hMap hPre g

example {L : P ⥤ (A ⥤ A)} {R : Pᵒᵖ ⥤ (A ⥤ A)} (a : L ⊣₂ R)
    {S T : P} (f : S ⟶ T) (unitIso : R.obj (.op T) ≅ 𝟭 A) (X : A) :
    ((a.adj S).homEquiv X X)
      ((L.map f).app X ≫ (leftUnitIso (a.adj T) unitIso).hom.app X) =
      unitIso.inv.app X ≫ (R.map f.op).app X :=
  sourcePre_unit_adjoint a f unitIso X

example {L : P ⥤ (A ⥤ A)} {R : Pᵒᵖ ⥤ (A ⥤ A)} (a : L ⊣₂ R)
    {S T : P} (f : S ⟶ T) (unitIso : R.obj (.op T) ≅ 𝟭 A) (X : A) :
    ((a.adj S).homEquiv X X).symm (unitIso.inv.app X ≫ (R.map f.op).app X) =
      (L.map f).app X ≫ (leftUnitIso (a.adj T) unitIso).hom.app X :=
  sourcePre_unit_uncurried a f unitIso X

end IndependentCategories

section NonidentityParameter

universe w

-- Here P = ℕ, A = Type w, B = Type (w+1): the three categories cannot be identified.
example (L : ℕ ⥤ (Type w ⥤ Type (w + 1))) (R : ℕᵒᵖ ⥤ (Type (w + 1) ⥤ Type w))
    (a : L ⊣₂ R) (X : Type w) (Y : Type (w + 1)) (g : (L.obj 1).obj X ⟶ Y) :
    ((a.adj 0).homEquiv X Y) ((L.map (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _))).app X ≫ g) =
      ((a.adj 1).homEquiv X Y) g ≫
        (R.map (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _)).op).app Y :=
  sourcePre_adjoint_of_whole_eq a (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _))
    (L.obj 0) (L.obj 1) (R.obj (.op 0)) (R.obj (.op 1)) rfl rfl rfl rfl
    (a.adj 0) (a.adj 1) (HEq.refl _) (HEq.refl _)
    (L.map (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _)))
    (R.map (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _)).op) (HEq.refl _) (HEq.refl _) g

-- Unit source mates also permit a different parameter category, with the same nonidentity arrow.
example (L : ℕ ⥤ (Type w ⥤ Type w)) (R : ℕᵒᵖ ⥤ (Type w ⥤ Type w))
    (a : L ⊣₂ R) (unitIso : R.obj (.op 1) ≅ 𝟭 (Type w)) (X : Type w) :
    ((a.adj 0).homEquiv X X)
      ((L.map (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _))).app X ≫
        (leftUnitIso (a.adj 1) unitIso).hom.app X) =
      unitIso.inv.app X ≫ (R.map (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _)).op).app X :=
  sourcePre_unit_adjoint a (homOfLE (show (0 : ℕ) ≤ 1 from Nat.zero_le _)) unitIso X

end NonidentityParameter

namespace PrefixSetClient

universe w

/-!
An inhabited family with three different categories and different component universes.
The left adjoint forms a product with the finite prefix `{i : ℕ | i ≤ n}`;
the right adjoint takes the universal preimage along every coordinate in that prefix.
The higher universe target contains subsets of pairs, rather than subsets of ℕ.
-/

/-- Form pairs whose first coordinate lies in the prefix and whose second lies in the input set. -/
def prefixImage (n : ℕ) (X : Set ℕ) : Set (ULift.{w + 1} (ℕ × ℕ)) :=
  {p | p.down.1 ≤ n ∧ p.down.2 ∈ X}

/-- Retain exactly the elements whose pairs at every prefix coordinate lie in the target set. -/
def prefixPreimage (n : ℕ) (Y : Set (ULift.{w + 1} (ℕ × ℕ))) : Set ℕ :=
  {x | ∀ i : ℕ, i ≤ n → (ULift.up (i, x) : ULift.{w + 1} (ℕ × ℕ)) ∈ Y}

/-- Prefix images and their universal preimages form a Galois connection. -/
theorem prefixGalois (n : ℕ) :
    GaloisConnection (prefixImage.{w} n) (prefixPreimage n) := by
  intro X Y
  constructor
  · intro h x hx i hi
    exact h ⟨hi, hx⟩
  · intro h p hp
    exact h hp.2 p.down.1 hp.1

/-- Prefix images form a covariant family of functors between distinct subset categories. -/
def leftFamily : ℕ ⥤ (Set ℕ ⥤ Set (ULift.{w + 1} (ℕ × ℕ))) where
  obj n := (prefixGalois.{w} n).monotone_l.functor
  map f :=
    { app X := homOfLE (by
        intro p hp
        exact ⟨hp.1.trans (leOfHom f), hp.2⟩)
      naturality _ _ _ := Subsingleton.elim _ _ }
  map_id _ := by
    ext X
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    ext X
    exact Subsingleton.elim _ _

/-- Universal prefix preimages form the contravariant family of right adjoints. -/
def rightFamily : ℕᵒᵖ ⥤ (Set (ULift.{w + 1} (ℕ × ℕ)) ⥤ Set ℕ) where
  obj n := (prefixGalois.{w} n.unop).monotone_u.functor
  map f :=
    { app Y := homOfLE (by
        intro x hx i hi
        exact hx i (hi.trans (leOfHom f.unop)))
      naturality _ _ _ := Subsingleton.elim _ _ }
  map_id _ := by
    ext Y
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    ext Y
    exact Subsingleton.elim _ _

/-- The actual prefix Galois connections assemble into a parametrized adjunction. -/
def familyAdjunction : leftFamily.{w} ⊣₂ rightFamily where
  adj n := (prefixGalois.{w} n).adjunction
  unit_whiskerRight_map _ := by
    ext X
    exact Subsingleton.elim _ _

/-- The source map enlarges the prefix from zero to one. -/
abbrev zeroToOne : (0 : ℕ) ⟶ 1 := homOfLE (Nat.zero_le _)

/-- The selected source map is not invertible in the parameter category. -/
theorem zeroToOne_not_iso : ¬ IsIso zeroToOne := by
  intro h
  exact Nat.zero_ne_one ((PartialOrder.isIso_iff_eq zeroToOne).mp h)

/-- The actual left adjoints differ at the two endpoints of the selected source map. -/
theorem leftFamily_nonconstant :
    (leftFamily.{w}.obj 0).obj ({0} : Set ℕ) ≠ (leftFamily.obj 1).obj ({0} : Set ℕ) := by
  intro h
  have h₁ : (ULift.up (1, 0) : ULift.{w + 1} (ℕ × ℕ)) ∈
      (leftFamily.obj 1).obj ({0} : Set ℕ) := ⟨le_rfl, rfl⟩
  have h₀ : (ULift.up (1, 0) : ULift.{w + 1} (ℕ × ℕ)) ∈
      (leftFamily.obj 0).obj ({0} : Set ℕ) := by
    rw [h]
    exact h₁
  exact (Nat.not_succ_le_zero 0) h₀.1

/-- The public API retains both actual functors, endpoint adjunctions and source maps. -/
theorem source_at_zero_one (X : Set ℕ) (Y : Set (ULift.{w + 1} (ℕ × ℕ)))
    (g : (leftFamily.obj 1).obj X ⟶ Y) :
    ((familyAdjunction.adj 0).homEquiv X Y) ((leftFamily.map zeroToOne).app X ≫ g) =
      ((familyAdjunction.adj 1).homEquiv X Y) g ≫ (rightFamily.map zeroToOne.op).app Y :=
  sourcePre_adjoint_of_whole_eq familyAdjunction zeroToOne
    (leftFamily.obj 0) (leftFamily.obj 1) (rightFamily.obj (.op 0)) (rightFamily.obj (.op 1))
    rfl rfl rfl rfl (familyAdjunction.adj 0) (familyAdjunction.adj 1)
    (HEq.refl _) (HEq.refl _) (leftFamily.map zeroToOne) (rightFamily.map zeroToOne.op)
    (HEq.refl _) (HEq.refl _) g

#print axioms prefixGalois
#print axioms familyAdjunction
#print axioms zeroToOne_not_iso
#print axioms leftFamily_nonconstant
#print axioms source_at_zero_one

end PrefixSetClient

end FunctionUnitClient
