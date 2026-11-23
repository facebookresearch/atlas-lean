/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.CategoryTheory.Monoidal.SInverseSBiprodFunctor

/-! # Tests for coordinatewise biproduct on additive S⁻¹S -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSBiprodFunctor

open CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check pairBiprodObj
#check biprodInterchangeIso
#check biprodInterchangeIso_naturality
#check biprodInterchangeIso_hom_ext
#check biprodInterchangeIso_zero_hom
#check RawHom.biprod
#check RawHom.biprod_stabilizer
#check RawHom.biprod_hom₁
#check RawHom.biprod_hom₂
#check RawHom.biprod_rel
#check Hom.biprod
#check Hom.biprod_mk
#check RawHom.biprod_id_rel
#check RawHom.biprod_comp_rel
#check Hom.biprod_comp
#check Hom.biprod_id
#check pairBiprodFunctor
#check pairBiprodFunctor_obj
#check pairBiprodFunctor_map

example (X Y : Pair C) :
    pairBiprodObj X Y = ⟨X.fst ⊞ Y.fst, X.snd ⊞ Y.snd⟩ :=
  rfl

example {A B X Y A' B' X' Y' : C}
    (a : A ⟶ A') (b : B ⟶ B') (x : X ⟶ X') (y : Y ⟶ Y') :
    biprod.map (biprod.map a b) (biprod.map x y) ≫
        (biprodInterchangeIso A' B' X' Y').hom =
      (biprodInterchangeIso A B X Y).hom ≫
        biprod.map (biprod.map a x) (biprod.map b y) :=
  biprodInterchangeIso_naturality a b x y

example {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    (f.biprod g).stabilizer = (f.stabilizer ⊞ g.stabilizer) :=
  RawHom.biprod_stabilizer f g

example {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    (f.biprod g).hom₁ =
      (biprodInterchangeIso
        f.stabilizer g.stabilizer X.fst Y.fst).trans
        (biprod.mapIso f.hom₁ g.hom₁) :=
  RawHom.biprod_hom₁ f g

example {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    (f.biprod g).hom₂ =
      (biprodInterchangeIso
        f.stabilizer g.stabilizer X.snd Y.snd).trans
        (biprod.mapIso f.hom₂ g.hom₂) :=
  RawHom.biprod_hom₂ f g

example {X X' Y Y' : Pair C}
    {f f' : RawHom X X'} {g g' : RawHom Y Y'}
    (hf : f.Rel f') (hg : g.Rel g') :
    (f.biprod g).Rel (f'.biprod g') :=
  RawHom.biprod_rel hf hg

example {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    Hom.biprod (Hom.mk f) (Hom.mk g) = Hom.mk (f.biprod g) :=
  Hom.biprod_mk f g

example (X Y : Pair C) :
    ((RawHom.id X).biprod (RawHom.id Y)).Rel
      (RawHom.id (pairBiprodObj X Y)) :=
  RawHom.biprod_id_rel X Y

example (X Y : Pair C) :
    Hom.biprod (𝟙 X) (𝟙 Y) = 𝟙 (pairBiprodObj X Y) :=
  Hom.biprod_id X Y

example {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Pair C}
    (f₀ : RawHom X₀ X₁) (f₁ : RawHom X₁ X₂)
    (g₀ : RawHom Y₀ Y₁) (g₁ : RawHom Y₁ Y₂) :
    ((f₀.comp f₁).biprod (g₀.comp g₁)).Rel
      ((f₀.biprod g₀).comp (f₁.biprod g₁)) :=
  RawHom.biprod_comp_rel f₀ f₁ g₀ g₁

example {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Pair C}
    (f₀ : RawHom X₀ X₁) (f₁ : RawHom X₁ X₂)
    (g₀ : RawHom Y₀ Y₁) (g₁ : RawHom Y₁ Y₂) :
    ((f₀.comp f₁).biprod (g₀.comp g₁)).stabilizer =
      ((f₁.stabilizer ⊞ f₀.stabilizer) ⊞
        (g₁.stabilizer ⊞ g₀.stabilizer)) :=
  rfl

example {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Pair C}
    (f₀ : RawHom X₀ X₁) (f₁ : RawHom X₁ X₂)
    (g₀ : RawHom Y₀ Y₁) (g₁ : RawHom Y₁ Y₂) :
    ((f₀.biprod g₀).comp (f₁.biprod g₁)).stabilizer =
      ((f₁.stabilizer ⊞ g₁.stabilizer) ⊞
        (f₀.stabilizer ⊞ g₀.stabilizer)) :=
  rfl

example {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Pair C}
    (f₀ : Hom X₀ X₁) (f₁ : Hom X₁ X₂)
    (g₀ : Hom Y₀ Y₁) (g₁ : Hom Y₁ Y₂) :
    Hom.biprod (Hom.comp f₀ f₁) (Hom.comp g₀ g₁) =
      Hom.comp (Hom.biprod f₀ g₀) (Hom.biprod f₁ g₁) :=
  Hom.biprod_comp f₀ f₁ g₀ g₁

example (X Y : Pair C) :
    pairBiprodFunctor.obj (X, Y) = pairBiprodObj X Y :=
  pairBiprodFunctor_obj (X, Y)

example {X Y : Pair C × Pair C} (f : X ⟶ Y) :
    pairBiprodFunctor.map f = Hom.biprod f.1 f.2 :=
  pairBiprodFunctor_map f

example (X Y : Pair C) :
    pairBiprodFunctor.map (𝟙 (X, Y)) = 𝟙 (pairBiprodObj X Y) := by
  simp

example {X Y Z : Pair C × Pair C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pairBiprodFunctor.map (f ≫ g) =
      pairBiprodFunctor.map f ≫ pairBiprodFunctor.map g :=
  pairBiprodFunctor.map_comp f g

private abbrev ZeroCategory := SingleObj (ZMod 1)

private instance (X Y : ZeroCategory) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ZMod 1))

private instance : HasZeroObject ZeroCategory where
  zero :=
    ⟨SingleObj.star (ZMod 1),
      (IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)⟩

private instance : HasBinaryBiproducts ZeroCategory where
  has_binary_biproduct X Y := by
    apply hasBinaryBiproduct_of_total
      { pt := SingleObj.star (ZMod 1)
        fst := 0
        snd := 0
        inl := 0
        inr := 0
        inl_fst := Subsingleton.elim _ _
        inl_snd := Subsingleton.elim _ _
        inr_fst := Subsingleton.elim _ _
        inr_snd := Subsingleton.elim _ _ }
    exact Subsingleton.elim _ _

private abbrev zeroPair : Pair ZeroCategory :=
  ⟨SingleObj.star (ZMod 1), SingleObj.star (ZMod 1)⟩

example :
    pairBiprodFunctor.obj (zeroPair, zeroPair) =
      pairBiprodObj zeroPair zeroPair :=
  rfl

example :
    pairBiprodFunctor.map (𝟙 (zeroPair, zeroPair)) =
      𝟙 (pairBiprodObj zeroPair zeroPair) := by
  simp

section RaisedUniverses

variable {C₁ : Type 1} [Category.{1} C₁] [HasZeroMorphisms C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁]

example (X Y : Pair C₁) :
    pairBiprodFunctor.obj (X, Y) = pairBiprodObj X Y :=
  pairBiprodFunctor_obj (X, Y)

example {X Y : Pair C₁ × Pair C₁} (f : X ⟶ Y) :
    pairBiprodFunctor.map f = Hom.biprod f.1 f.2 :=
  pairBiprodFunctor_map f

end RaisedUniverses

#print axioms pairBiprodObj
#print axioms biprodInterchangeIso
#print axioms biprodInterchangeIso_naturality
#print axioms biprodInterchangeIso_hom_ext
#print axioms biprodInterchangeIso_zero_hom
#print axioms RawHom.biprod
#print axioms RawHom.biprod_stabilizer
#print axioms RawHom.biprod_hom₁
#print axioms RawHom.biprod_hom₂
#print axioms RawHom.biprod_rel
#print axioms Hom.biprod
#print axioms Hom.biprod_mk
#print axioms RawHom.biprod_id_rel
#print axioms RawHom.biprod_comp_rel
#print axioms Hom.biprod_comp
#print axioms Hom.biprod_id
#print axioms pairBiprodFunctor
#print axioms pairBiprodFunctor_obj
#print axioms pairBiprodFunctor_map

end MathlibExtTest.SInverseSBiprodFunctor

end
