/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS

/-!
# Coordinatewise biproduct on additive S⁻¹S

Coordinatewise biproduct of pairs and stabilized arrows descends through the
stabilizer quotient to a bifunctor on the additive `S⁻¹S` category.

The load-bearing coherence is the four-object shuffle
`(A ⊞ B) ⊞ (X ⊞ Y) ≅ (A ⊞ X) ⊞ (B ⊞ Y)`.  It reorders the two stabilizers
against the two source coordinates.  This file constructs only the bifunctor;
it makes no zero-component, unital, monoidal, realization, H-space, homology,
or plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Coordinatewise biproduct of two objects of additive `S⁻¹S`. -/
abbrev pairBiprodObj (X Y : Pair C) : Pair C :=
  ⟨X.fst ⊞ Y.fst, X.snd ⊞ Y.snd⟩

/-- The canonical middle-four interchange for chosen biproducts. -/
noncomputable def biprodInterchangeIso (A B X Y : C) :
    (A ⊞ B) ⊞ (X ⊞ Y) ≅ (A ⊞ X) ⊞ (B ⊞ Y) where
  hom := biprod.desc
    (biprod.desc
      (biprod.inl ≫ biprod.inl)
      (biprod.inl ≫ biprod.inr))
    (biprod.desc
      (biprod.inr ≫ biprod.inl)
      (biprod.inr ≫ biprod.inr))
  inv := biprod.desc
    (biprod.desc
      (biprod.inl ≫ biprod.inl)
      (biprod.inl ≫ biprod.inr))
    (biprod.desc
      (biprod.inr ≫ biprod.inl)
      (biprod.inr ≫ biprod.inr))
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext' <;> simp
    · apply biprod.hom_ext' <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext' <;> simp
    · apply biprod.hom_ext' <;> simp

/-- Naturality of the middle-four interchange in all four entries. -/
theorem biprodInterchangeIso_naturality
    {A B X Y A' B' X' Y' : C}
    (a : A ⟶ A') (b : B ⟶ B') (x : X ⟶ X') (y : Y ⟶ Y') :
    biprod.map (biprod.map a b) (biprod.map x y) ≫
        (biprodInterchangeIso A' B' X' Y').hom =
      (biprodInterchangeIso A B X Y).hom ≫
        biprod.map (biprod.map a x) (biprod.map b y) := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext' <;> simp [biprodInterchangeIso, Category.assoc]
  · apply biprod.hom_ext' <;> simp [biprodInterchangeIso, Category.assoc]

/-- Coordinate formulas characterize the interchange map. -/
theorem biprodInterchangeIso_hom_ext
    (A B X Y : C) :
    (biprodInterchangeIso A B X Y).hom =
      biprod.desc
        (biprod.desc
          (biprod.inl ≫ biprod.inl)
          (biprod.inl ≫ biprod.inr))
        (biprod.desc
          (biprod.inr ≫ biprod.inl)
          (biprod.inr ≫ biprod.inr)) := by
  rfl

section ZeroObject

variable [HasZeroObject C]

/-- Removing the tensor of two zero stabilizers commutes with the
middle-four interchange. -/
theorem biprodInterchangeIso_zero_hom (X Y : C) :
    biprod.map
          (isoZeroBiprod (isZero_zero C)).symm.hom
          (𝟙 (X ⊞ Y)) ≫
        (isoZeroBiprod (isZero_zero C)).symm.hom =
      (biprodInterchangeIso (0 : C) (0 : C) X Y).hom ≫
        biprod.map
          (isoZeroBiprod (isZero_zero C)).symm.hom
          (isoZeroBiprod (isZero_zero C)).symm.hom := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext' <;>
      simp [biprodInterchangeIso, Category.assoc]
  · apply biprod.hom_ext' <;>
      simp [biprodInterchangeIso, Category.assoc]

end ZeroObject

namespace RawHom

/-- Coordinatewise biproduct of raw stabilized arrows. -/
noncomputable abbrev biprod {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    RawHom (pairBiprodObj X Y) (pairBiprodObj X' Y') where
  stabilizer := f.stabilizer ⊞ g.stabilizer
  hom₁ := (biprodInterchangeIso f.stabilizer g.stabilizer X.fst Y.fst).trans
    (biprod.mapIso f.hom₁ g.hom₁)
  hom₂ := (biprodInterchangeIso f.stabilizer g.stabilizer X.snd Y.snd).trans
    (biprod.mapIso f.hom₂ g.hom₂)

@[simp]
theorem biprod_stabilizer {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    (f.biprod g).stabilizer = (f.stabilizer ⊞ g.stabilizer) :=
  rfl

@[simp]
theorem biprod_hom₁ {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    (f.biprod g).hom₁ =
      (biprodInterchangeIso f.stabilizer g.stabilizer X.fst Y.fst).trans
        (biprod.mapIso f.hom₁ g.hom₁) :=
  rfl

@[simp]
theorem biprod_hom₂ {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    (f.biprod g).hom₂ =
      (biprodInterchangeIso f.stabilizer g.stabilizer X.snd Y.snd).trans
        (biprod.mapIso f.hom₂ g.hom₂) :=
  rfl

/-- Coordinatewise biproduct respects change of stabilizer in both raw
arrows. -/
theorem biprod_rel {X X' Y Y' : Pair C}
    {f f' : RawHom X X'} {g g' : RawHom Y Y'}
    (hf : f.Rel f') (hg : g.Rel g') :
    (f.biprod g).Rel (f'.biprod g') := by
  obtain ⟨e, hf₁, hf₂⟩ := hf
  obtain ⟨d, hg₁, hg₂⟩ := hg
  refine ⟨biprod.mapIso e d, ?_, ?_⟩
  · apply Iso.ext
    have hf₁' := congrArg Iso.hom hf₁
    have hg₁' := congrArg Iso.hom hg₁
    change biprod.map e.hom (𝟙 X.fst) ≫ f'.hom₁.hom =
      f.hom₁.hom at hf₁'
    change biprod.map d.hom (𝟙 Y.fst) ≫ g'.hom₁.hom =
      g.hom₁.hom at hg₁'
    have hnat := biprodInterchangeIso_naturality
      e.hom d.hom (𝟙 X.fst) (𝟙 Y.fst)
    have hid : biprod.map (𝟙 X.fst) (𝟙 Y.fst) =
        𝟙 (X.fst ⊞ Y.fst) := by
      apply biprod.hom_ext <;> simp
    rw [hid] at hnat
    have hmap :
        biprod.map
              (biprod.map e.hom (𝟙 X.fst))
              (biprod.map d.hom (𝟙 Y.fst)) ≫
            biprod.map f'.hom₁.hom g'.hom₁.hom =
          biprod.map f.hom₁.hom g.hom₁.hom := by
      apply biprod.hom_ext <;>
        simp [Category.assoc, hf₁', hg₁']
    dsimp [RawHom.biprod, stabilizerIso]
    simp only [biprod.mapIso_hom, Iso.refl_hom]
    rw [← Category.assoc, hnat, Category.assoc, hmap]
  · apply Iso.ext
    have hf₂' := congrArg Iso.hom hf₂
    have hg₂' := congrArg Iso.hom hg₂
    change biprod.map e.hom (𝟙 X.snd) ≫ f'.hom₂.hom =
      f.hom₂.hom at hf₂'
    change biprod.map d.hom (𝟙 Y.snd) ≫ g'.hom₂.hom =
      g.hom₂.hom at hg₂'
    have hnat := biprodInterchangeIso_naturality
      e.hom d.hom (𝟙 X.snd) (𝟙 Y.snd)
    have hid : biprod.map (𝟙 X.snd) (𝟙 Y.snd) =
        𝟙 (X.snd ⊞ Y.snd) := by
      apply biprod.hom_ext <;> simp
    rw [hid] at hnat
    have hmap :
        biprod.map
              (biprod.map e.hom (𝟙 X.snd))
              (biprod.map d.hom (𝟙 Y.snd)) ≫
            biprod.map f'.hom₂.hom g'.hom₂.hom =
          biprod.map f.hom₂.hom g.hom₂.hom := by
      apply biprod.hom_ext <;>
        simp [Category.assoc, hf₂', hg₂']
    dsimp [RawHom.biprod, stabilizerIso]
    simp only [biprod.mapIso_hom, Iso.refl_hom]
    rw [← Category.assoc, hnat, Category.assoc, hmap]

end RawHom

/-- Coordinatewise biproduct of quotient stabilized arrows. -/
noncomputable def Hom.biprod {X X' Y Y' : Pair C}
    (f : Hom X X') (g : Hom Y Y') :
    Hom (pairBiprodObj X Y) (pairBiprodObj X' Y') :=
  Quotient.map₂ RawHom.biprod
    (fun _ _ hf _ _ hg ↦ RawHom.biprod_rel hf hg) f g

@[simp]
theorem Hom.biprod_mk {X X' Y Y' : Pair C}
    (f : RawHom X X') (g : RawHom Y Y') :
    Hom.biprod (Hom.mk f) (Hom.mk g) = Hom.mk (f.biprod g) :=
  rfl

namespace RawHom

section ZeroObject

variable [HasZeroObject C]

/-- The coordinatewise biproduct of two raw identities agrees with the raw
identity after changing the stabilizer `0 ⊞ 0` to `0`. -/
theorem biprod_id_rel (X Y : Pair C) :
    ((RawHom.id X).biprod (RawHom.id Y)).Rel
      (RawHom.id (pairBiprodObj X Y)) := by
  refine ⟨(isoZeroBiprod (isZero_zero C)).symm, ?_, ?_⟩
  · apply Iso.ext
    dsimp [RawHom.biprod, RawHom.id, stabilizerIso]
    exact biprodInterchangeIso_zero_hom X.fst Y.fst
  · apply Iso.ext
    dsimp [RawHom.biprod, RawHom.id, stabilizerIso]
    exact biprodInterchangeIso_zero_hom X.snd Y.snd

end ZeroObject

end RawHom

@[reassoc (attr := simp)]
private theorem biprodInterchangeIso_inl_inl
    (A B X Y : C) :
    (biprod.inl : A ⟶ A ⊞ B) ≫
        (biprod.inl : A ⊞ B ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inl : A ⟶ A ⊞ X) ≫
        (biprod.inl : A ⊞ X ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  simp [biprodInterchangeIso]

@[reassoc (attr := simp)]
private theorem biprodInterchangeIso_inr_inl
    (A B X Y : C) :
    (biprod.inr : B ⟶ A ⊞ B) ≫
        (biprod.inl : A ⊞ B ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inl : B ⟶ B ⊞ Y) ≫
        (biprod.inr : B ⊞ Y ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  simp [biprodInterchangeIso]

@[reassoc (attr := simp)]
private theorem biprodInterchangeIso_inl_inr
    (A B X Y : C) :
    (biprod.inl : X ⟶ X ⊞ Y) ≫
        (biprod.inr : X ⊞ Y ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inr : X ⟶ A ⊞ X) ≫
        (biprod.inl : A ⊞ X ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  simp [biprodInterchangeIso]

@[reassoc (attr := simp)]
private theorem biprodInterchangeIso_inr_inr
    (A B X Y : C) :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫
        (biprod.inr : X ⊞ Y ⟶ (A ⊞ B) ⊞ (X ⊞ Y)) ≫
        (biprodInterchangeIso A B X Y).hom =
      (biprod.inr : Y ⟶ B ⊞ Y) ≫
        (biprod.inr : B ⊞ Y ⟶ (A ⊞ X) ⊞ (B ⊞ Y)) := by
  simp [biprodInterchangeIso]

@[reassoc (attr := simp)]
private theorem biprod_inl_inl_associator_hom (A B X : C) :
    (biprod.inl : A ⟶ A ⊞ B) ≫
        (biprod.inl : A ⊞ B ⟶ (A ⊞ B) ⊞ X) ≫
        (biprod.associator A B X).hom =
      (biprod.inl : A ⟶ A ⊞ (B ⊞ X)) := by
  cat_disch

@[reassoc (attr := simp)]
private theorem biprod_inr_inl_associator_hom (A B X : C) :
    (biprod.inr : B ⟶ A ⊞ B) ≫
        (biprod.inl : A ⊞ B ⟶ (A ⊞ B) ⊞ X) ≫
        (biprod.associator A B X).hom =
      (biprod.inl : B ⟶ B ⊞ X) ≫
        (biprod.inr : B ⊞ X ⟶ A ⊞ (B ⊞ X)) := by
  cat_disch

@[reassoc (attr := simp)]
private theorem biprod_inr_associator_hom (A B X : C) :
    (biprod.inr : X ⟶ (A ⊞ B) ⊞ X) ≫
        (biprod.associator A B X).hom =
      (biprod.inr : X ⟶ B ⊞ X) ≫
        (biprod.inr : B ⊞ X ⟶ A ⊞ (B ⊞ X)) := by
  cat_disch

set_option linter.unusedSimpArgs false in
set_option linter.flexible false in
private theorem biprodInterchangeIso_associator_hom
    (a b c d X Y : C) :
    biprod.map (biprodInterchangeIso b a d c).hom (𝟙 (X ⊞ Y)) ≫
          (biprod.associator (b ⊞ d) (a ⊞ c) (X ⊞ Y)).hom ≫
          biprod.map (𝟙 (b ⊞ d))
            (biprodInterchangeIso a c X Y).hom ≫
          (biprodInterchangeIso b d (a ⊞ X) (c ⊞ Y)).hom =
      (biprodInterchangeIso (b ⊞ a) (d ⊞ c) X Y).hom ≫
        biprod.map
          (biprod.associator b a X).hom
          (biprod.associator d c Y).hom := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · apply biprod.hom_ext' <;>
        simp only [Category.assoc, Category.id_comp, Category.comp_id,
          biprod.inl_map_assoc, biprod.inr_map_assoc,
          biprodInterchangeIso_inl_inl_assoc,
          biprodInterchangeIso_inr_inl_assoc,
          biprodInterchangeIso_inl_inr_assoc,
          biprodInterchangeIso_inr_inr_assoc,
          biprod_inl_inl_associator_hom_assoc,
          biprod_inr_inl_associator_hom_assoc,
          biprod_inr_associator_hom_assoc] <;>
        simp [biprodInterchangeIso, Category.assoc] <;>
        cat_disch
    · apply biprod.hom_ext' <;>
        simp only [Category.assoc, Category.id_comp, Category.comp_id,
          biprod.inl_map_assoc, biprod.inr_map_assoc,
          biprodInterchangeIso_inl_inl_assoc,
          biprodInterchangeIso_inr_inl_assoc,
          biprodInterchangeIso_inl_inr_assoc,
          biprodInterchangeIso_inr_inr_assoc,
          biprod_inl_inl_associator_hom_assoc,
          biprod_inr_inl_associator_hom_assoc,
          biprod_inr_associator_hom_assoc] <;>
        simp [biprodInterchangeIso, Category.assoc] <;>
        cat_disch
  · apply biprod.hom_ext' <;>
      simp only [Category.assoc, Category.id_comp, Category.comp_id,
        biprod.inl_map_assoc, biprod.inr_map_assoc,
        biprodInterchangeIso_inl_inl_assoc,
        biprodInterchangeIso_inr_inl_assoc,
        biprodInterchangeIso_inl_inr_assoc,
        biprodInterchangeIso_inr_inr_assoc,
        biprod_inl_inl_associator_hom_assoc,
        biprod_inr_inl_associator_hom_assoc,
        biprod_inr_associator_hom_assoc] <;>
      simp [biprodInterchangeIso, Category.assoc] <;>
      cat_disch

private theorem biprodInterchangeIso_comp_hom
    {a b c d X X' X'' Y Y' Y'' : C}
    (f : a ⊞ X ⟶ X') (f' : b ⊞ X' ⟶ X'')
    (g : c ⊞ Y ⟶ Y') (g' : d ⊞ Y' ⟶ Y'') :
    biprod.map (biprodInterchangeIso b a d c).hom (𝟙 (X ⊞ Y)) ≫
          (biprod.associator (b ⊞ d) (a ⊞ c) (X ⊞ Y)).hom ≫
          biprod.map (𝟙 (b ⊞ d))
            ((biprodInterchangeIso a c X Y).hom ≫
              biprod.map f g) ≫
          (biprodInterchangeIso b d X' Y').hom ≫
          biprod.map f' g' =
      (biprodInterchangeIso (b ⊞ a) (d ⊞ c) X Y).hom ≫
        biprod.map
          ((biprod.associator b a X).hom ≫
            biprod.map (𝟙 b) f ≫ f')
          ((biprod.associator d c Y).hom ≫
            biprod.map (𝟙 d) g ≫ g') := by
  have hinner :
      biprod.map (𝟙 (b ⊞ d))
          ((biprodInterchangeIso a c X Y).hom ≫ biprod.map f g) =
        biprod.map (𝟙 (b ⊞ d))
            (biprodInterchangeIso a c X Y).hom ≫
          biprod.map (𝟙 (b ⊞ d)) (biprod.map f g) := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hbd : biprod.map (𝟙 b) (𝟙 d) = 𝟙 (b ⊞ d) := by
    apply biprod.hom_ext <;> simp
  have hnat := biprodInterchangeIso_naturality
    (𝟙 b) (𝟙 d) f g
  rw [hbd] at hnat
  have htail :
      biprod.map (biprod.map (𝟙 b) f) (biprod.map (𝟙 d) g) ≫
          biprod.map f' g' =
        biprod.map (biprod.map (𝟙 b) f ≫ f')
          (biprod.map (𝟙 d) g ≫ g') := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hfinal :
      biprod.map
            (biprod.associator b a X).hom
            (biprod.associator d c Y).hom ≫
          biprod.map (biprod.map (𝟙 b) f ≫ f')
            (biprod.map (𝟙 d) g ≫ g') =
        biprod.map
          ((biprod.associator b a X).hom ≫
            biprod.map (𝟙 b) f ≫ f')
          ((biprod.associator d c Y).hom ≫
            biprod.map (𝟙 d) g ≫ g') := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  rw [hinner]
  slice_lhs 4 5 => rw [hnat]
  slice_lhs 5 6 => rw [htail]
  slice_lhs 1 4 => rw [biprodInterchangeIso_associator_hom]
  slice_lhs 2 3 => rw [hfinal]

namespace RawHom

/-- Coordinatewise biproduct commutes with raw composition up to the
canonical shuffle of the four stabilizers. -/
theorem biprod_comp_rel
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Pair C}
    (f₀ : RawHom X₀ X₁) (f₁ : RawHom X₁ X₂)
    (g₀ : RawHom Y₀ Y₁) (g₁ : RawHom Y₁ Y₂) :
    ((f₀.comp f₁).biprod (g₀.comp g₁)).Rel
      ((f₀.biprod g₀).comp (f₁.biprod g₁)) := by
  refine ⟨biprodInterchangeIso
    f₁.stabilizer f₀.stabilizer g₁.stabilizer g₀.stabilizer, ?_, ?_⟩
  · apply Iso.ext
    dsimp [RawHom.comp, RawHom.biprod, stabilizerIso]
    exact biprodInterchangeIso_comp_hom
      f₀.hom₁.hom f₁.hom₁.hom g₀.hom₁.hom g₁.hom₁.hom
  · apply Iso.ext
    dsimp [RawHom.comp, RawHom.biprod, stabilizerIso]
    exact biprodInterchangeIso_comp_hom
      f₀.hom₂.hom f₁.hom₂.hom g₀.hom₂.hom g₁.hom₂.hom

end RawHom

/-- Coordinatewise biproduct preserves quotient composition. -/
theorem Hom.biprod_comp
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Pair C}
    (f₀ : Hom X₀ X₁) (f₁ : Hom X₁ X₂)
    (g₀ : Hom Y₀ Y₁) (g₁ : Hom Y₁ Y₂) :
    Hom.biprod (Hom.comp f₀ f₁) (Hom.comp g₀ g₁) =
      Hom.comp (Hom.biprod f₀ g₀) (Hom.biprod f₁ g₁) := by
  induction f₀ using Quotient.inductionOn with
  | _ f₀ =>
    induction f₁ using Quotient.inductionOn with
    | _ f₁ =>
      induction g₀ using Quotient.inductionOn with
      | _ g₀ =>
        induction g₁ using Quotient.inductionOn with
        | _ g₁ =>
          apply Quotient.sound
          exact RawHom.biprod_comp_rel f₀ f₁ g₀ g₁

section ZeroObject

variable [HasZeroObject C]

/-- Coordinatewise biproduct preserves quotient identities. -/
@[simp]
theorem Hom.biprod_id (X Y : Pair C) :
    Hom.biprod (𝟙 X) (𝟙 Y) = 𝟙 (pairBiprodObj X Y) := by
  change Hom.biprod (Hom.id X) (Hom.id Y) =
    Hom.id (pairBiprodObj X Y)
  apply Quotient.sound
  exact RawHom.biprod_id_rel X Y

/-- Coordinatewise biproduct as a bifunctor on additive `S⁻¹S` pairs. -/
noncomputable def pairBiprodFunctor : Pair C × Pair C ⥤ Pair C where
  obj X := pairBiprodObj X.1 X.2
  map f := Hom.biprod f.1 f.2
  map_id X := Hom.biprod_id X.1 X.2
  map_comp f g := Hom.biprod_comp f.1 g.1 f.2 g.2

/-- Object formula for the coordinatewise biproduct bifunctor. -/
@[simp]
theorem pairBiprodFunctor_obj (X : Pair C × Pair C) :
    (pairBiprodFunctor.obj X) = pairBiprodObj X.1 X.2 :=
  rfl

/-- Morphism formula for the coordinatewise biproduct bifunctor. -/
@[simp]
theorem pairBiprodFunctor_map {X Y : Pair C × Pair C} (f : X ⟶ Y) :
    pairBiprodFunctor.map f = Hom.biprod f.1 f.2 :=
  rfl

end ZeroObject

end SInverseS
end CategoryTheory

end
