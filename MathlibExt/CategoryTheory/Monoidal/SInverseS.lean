/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Faithful biproduct translations for the S⁻¹S construction

The group-completion theorem for Quillen's `S⁻¹S` construction assumes
that translation by any object acts injectively on automorphism groups.  In
an additive category this follows formally from the split inclusions into a
binary biproduct.

This file packages the two automorphism homomorphisms `f ↦ f ⊞ id` and
`g ↦ id ⊞ g` and proves that both are injective.  It does not yet define
the quotient category `S⁻¹S` or assert a group-completion theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Translation on automorphisms by adding a fixed right biproduct
summand. -/
noncomputable def biprodRightAutHom (A B : C) : Aut A →* Aut (A ⊞ B) where
  toFun f := .of (biprod.mapIso f.asIso (Iso.refl B))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change biprod.map (𝟙 A) (𝟙 B) = 𝟙 (A ⊞ B)
    ext <;> simp
  map_mul' f g := by
    apply Aut.ext
    apply Iso.ext
    change biprod.map (g.asIso.hom ≫ f.asIso.hom) (𝟙 B) =
      biprod.map g.asIso.hom (𝟙 B) ≫ biprod.map f.asIso.hom (𝟙 B)
    ext <;> simp

@[simp]
theorem biprodRightAutHom_apply (A B : C) (f : Aut A) :
    biprodRightAutHom A B f = .of (biprod.mapIso f.asIso (Iso.refl B)) :=
  rfl

/-- Right biproduct translation is faithful on automorphism groups. -/
theorem biprodRightAutHom_injective (A B : C) :
    Function.Injective (biprodRightAutHom A B) := by
  intro f g h
  apply Aut.ext
  apply Iso.ext
  have hHom := congrArg (fun a : Aut (A ⊞ B) => a.asIso.hom) h
  change biprod.map f.asIso.hom (𝟙 B) = biprod.map g.asIso.hom (𝟙 B) at hHom
  have hInl := congrArg (fun k => (biprod.inl : A ⟶ A ⊞ B) ≫ k) hHom
  rw [biprod.inl_map, biprod.inl_map] at hInl
  exact (cancel_mono (biprod.inl : A ⟶ A ⊞ B)).1 hInl

/-- Translation on automorphisms by adding a fixed left biproduct
summand. -/
noncomputable def biprodLeftAutHom (A B : C) : Aut B →* Aut (A ⊞ B) where
  toFun g := .of (biprod.mapIso (Iso.refl A) g.asIso)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change biprod.map (𝟙 A) (𝟙 B) = 𝟙 (A ⊞ B)
    ext <;> simp
  map_mul' f g := by
    apply Aut.ext
    apply Iso.ext
    change biprod.map (𝟙 A) (g.asIso.hom ≫ f.asIso.hom) =
      biprod.map (𝟙 A) g.asIso.hom ≫ biprod.map (𝟙 A) f.asIso.hom
    ext <;> simp

@[simp]
theorem biprodLeftAutHom_apply (A B : C) (g : Aut B) :
    biprodLeftAutHom A B g = .of (biprod.mapIso (Iso.refl A) g.asIso) :=
  rfl

/-- Left biproduct translation is faithful on automorphism groups. -/
theorem biprodLeftAutHom_injective (A B : C) :
    Function.Injective (biprodLeftAutHom A B) := by
  intro f g h
  apply Aut.ext
  apply Iso.ext
  have hHom := congrArg (fun a : Aut (A ⊞ B) => a.asIso.hom) h
  change biprod.map (𝟙 A) f.asIso.hom = biprod.map (𝟙 A) g.asIso.hom at hHom
  have hInr := congrArg (fun k => (biprod.inr : B ⟶ A ⊞ B) ≫ k) hHom
  rw [biprod.inr_map, biprod.inr_map] at hInr
  exact (cancel_mono (biprod.inr : B ⟶ A ⊞ B)).1 hInr

/-! ## Raw stabilized arrows -/

/-- Objects underlying the additive `S⁻¹S` presentation are ordered pairs
of objects.  This is a new type rather than `C × C`, so it can carry the
stabilizer-quotient category structure instead of the product category. -/
structure Pair (C : Type u) where
  /-- First coordinate. -/
  fst : C
  /-- Second coordinate. -/
  snd : C

/-- A raw stabilized arrow from `X` to `Y`: a common stabilizer `s` and
isomorphisms from `s ⊞ Xᵢ` to `Yᵢ` in both coordinates. -/
structure RawHom (X Y : Pair C) where
  /-- The common stabilizing object. -/
  stabilizer : C
  /-- The first-coordinate stabilized isomorphism. -/
  hom₁ : stabilizer ⊞ X.fst ≅ Y.fst
  /-- The second-coordinate stabilized isomorphism. -/
  hom₂ : stabilizer ⊞ X.snd ≅ Y.snd

/-- Change a stabilizer along an isomorphism, leaving the translated object
fixed. -/
noncomputable def stabilizerIso {s t : C} (e : s ≅ t) (X : C) :
    s ⊞ X ≅ t ⊞ X :=
  biprod.mapIso e (Iso.refl X)

@[simp]
theorem stabilizerIso_refl (s X : C) :
    stabilizerIso (Iso.refl s) X = Iso.refl (s ⊞ X) := by
  apply Iso.ext
  change biprod.map (𝟙 s) (𝟙 X) = 𝟙 (s ⊞ X)
  ext <;> simp

theorem stabilizerIso_trans {s t u : C} (e : s ≅ t) (f : t ≅ u)
    (X : C) :
    (stabilizerIso e X).trans (stabilizerIso f X) =
      stabilizerIso (e.trans f) X := by
  apply Iso.ext
  change biprod.map e.hom (𝟙 X) ≫ biprod.map f.hom (𝟙 X) =
    biprod.map (e.hom ≫ f.hom) (𝟙 X)
  ext <;> simp

/-- Two raw arrows agree when an isomorphism of their stabilizers identifies
both stabilized coordinate isomorphisms. -/
def RawHom.Rel {X Y : Pair C} (f g : RawHom X Y) : Prop :=
  ∃ e : f.stabilizer ≅ g.stabilizer,
    (stabilizerIso e X.fst).trans g.hom₁ = f.hom₁ ∧
      (stabilizerIso e X.snd).trans g.hom₂ = f.hom₂

theorem RawHom.Rel.refl {X Y : Pair C} (f : RawHom X Y) : f.Rel f := by
  refine ⟨Iso.refl f.stabilizer, ?_, ?_⟩
  · rw [stabilizerIso_refl, Iso.refl_trans]
  · rw [stabilizerIso_refl, Iso.refl_trans]

theorem RawHom.Rel.symm {X Y : Pair C} {f g : RawHom X Y}
    (h : f.Rel g) : g.Rel f := by
  obtain ⟨e, h₁, h₂⟩ := h
  refine ⟨e.symm, ?_, ?_⟩
  · rw [← h₁, ← Iso.trans_assoc, stabilizerIso_trans]
    simp
  · rw [← h₂, ← Iso.trans_assoc, stabilizerIso_trans]
    simp

theorem RawHom.Rel.trans {X Y : Pair C} {f g h : RawHom X Y}
    (hfg : f.Rel g) (hgh : g.Rel h) : f.Rel h := by
  obtain ⟨e, hfg₁, hfg₂⟩ := hfg
  obtain ⟨d, hgh₁, hgh₂⟩ := hgh
  refine ⟨e.trans d, ?_, ?_⟩
  · rw [← stabilizerIso_trans, Iso.trans_assoc, hgh₁, hfg₁]
  · rw [← stabilizerIso_trans, Iso.trans_assoc, hgh₂, hfg₂]

/-- The setoid of raw stabilized arrows modulo change of stabilizer. -/
noncomputable instance rawHomSetoid (X Y : Pair C) : Setoid (RawHom X Y) where
  r := RawHom.Rel
  iseqv := ⟨RawHom.Rel.refl, RawHom.Rel.symm, RawHom.Rel.trans⟩

/-- Stabilized arrows modulo isomorphism of the common stabilizer. -/
abbrev Hom (X Y : Pair C) := Quotient (rawHomSetoid X Y)

/-- Insert a raw stabilized arrow into the quotient hom type. -/
def Hom.mk {X Y : Pair C} (f : RawHom X Y) : Hom X Y :=
  Quotient.mk _ f

/-- Chosen raw representative of a quotient stabilized arrow. -/
noncomputable def Hom.representative {X Y : Pair C} (f : Hom X Y) :
    RawHom X Y :=
  Quotient.out f

@[simp]
theorem Hom.mk_representative {X Y : Pair C} (f : Hom X Y) :
    Hom.mk f.representative = f :=
  Quotient.out_eq f

/-! ## Raw composition -/

/-- Composition before passing to the stabilizer quotient.  The composite
of an `s`-stabilized arrow followed by a `t`-stabilized arrow is stabilized
by `t ⊞ s`. -/
noncomputable abbrev RawHom.comp {X Y Z : Pair C}
    (f : RawHom X Y) (g : RawHom Y Z) : RawHom X Z where
  stabilizer := g.stabilizer ⊞ f.stabilizer
  hom₁ := (biprod.associator g.stabilizer f.stabilizer X.fst).trans
    ((biprod.mapIso (Iso.refl g.stabilizer) f.hom₁).trans g.hom₁)
  hom₂ := (biprod.associator g.stabilizer f.stabilizer X.snd).trans
    ((biprod.mapIso (Iso.refl g.stabilizer) f.hom₂).trans g.hom₂)

/-- One-coordinate coherence for composition after changing both
stabilizers. -/
theorem rawComp_changeStabilizer_hom
    {s s' t t' X Y Z : C} (es : s ⟶ s') (et : t ⟶ t')
    (f : s' ⊞ X ⟶ Y) (g : t' ⊞ Y ⟶ Z) :
    biprod.map (biprod.map et es) (𝟙 X) ≫
          (biprod.associator t' s' X).hom ≫
          biprod.map (𝟙 t') f ≫ g =
      (biprod.associator t s X).hom ≫
          biprod.map (𝟙 t) (biprod.map es (𝟙 X) ≫ f) ≫
          biprod.map et (𝟙 Y) ≫ g := by
  rw [biprod.associator_natural_assoc]
  have hmap :
      biprod.map et (biprod.map es (𝟙 X)) ≫ biprod.map (𝟙 t') f =
        biprod.map (𝟙 t) (biprod.map es (𝟙 X) ≫ f) ≫
          biprod.map et (𝟙 Y) := by
    ext <;> simp
  rw [← Category.assoc
      (biprod.map et (biprod.map es (𝟙 X))) (biprod.map (𝟙 t') f) g,
    ← Category.assoc
      (biprod.map (𝟙 t) (biprod.map es (𝟙 X) ≫ f))
        (biprod.map et (𝟙 Y)) g,
    hmap]

/-- Raw composition respects change of stabilizer in both inputs. -/
theorem RawHom.comp_rel {X Y Z : Pair C}
    {f f' : RawHom X Y} {g g' : RawHom Y Z}
    (hf : f.Rel f') (hg : g.Rel g') :
    (f.comp g).Rel (f'.comp g') := by
  obtain ⟨ef, hf₁, hf₂⟩ := hf
  obtain ⟨eg, hg₁, hg₂⟩ := hg
  refine ⟨biprod.mapIso eg ef, ?_, ?_⟩
  · dsimp only [RawHom.comp]
    rw [← hf₁, ← hg₁]
    apply Iso.ext
    dsimp [stabilizerIso]
    exact rawComp_changeStabilizer_hom ef.hom eg.hom
      f'.hom₁.hom g'.hom₁.hom
  · dsimp only [RawHom.comp]
    rw [← hf₂, ← hg₂]
    apply Iso.ext
    dsimp [stabilizerIso]
    exact rawComp_changeStabilizer_hom ef.hom eg.hom
      f'.hom₂.hom g'.hom₂.hom

/-- Composition on quotient stabilized arrows. -/
noncomputable def Hom.comp {X Y Z : Pair C}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.map₂ RawHom.comp
    (fun _ _ hf _ _ hg => RawHom.comp_rel hf hg) f g

@[simp]
theorem Hom.comp_mk {X Y Z : Pair C}
    (f : RawHom X Y) (g : RawHom Y Z) :
    Hom.comp (Hom.mk f) (Hom.mk g) = Hom.mk (f.comp g) :=
  rfl

section Zero

variable [HasZeroObject C]

/-- The raw identity arrow, stabilized by the zero object. -/
noncomputable def RawHom.id (X : Pair C) : RawHom X X where
  stabilizer := 0
  hom₁ := (isoZeroBiprod (isZero_zero C)).symm
  hom₂ := (isoZeroBiprod (isZero_zero C)).symm

/-- One-coordinate left-unit coherence for a stabilized morphism. -/
theorem rawId_comp_hom (s X : C) :
    biprod.map (isoBiprodZero (isZero_zero C)).symm.hom (𝟙 X) =
      (biprod.associator s (0 : C) X).hom ≫
        biprod.map (𝟙 s) (isoZeroBiprod (isZero_zero C)).symm.hom := by
  apply biprod.hom_ext <;> simp

/-- Left identity holds up to change of stabilizer. -/
theorem RawHom.id_comp_rel {X Y : Pair C} (f : RawHom X Y) :
    (RawHom.id X).comp f |>.Rel f := by
  refine ⟨(isoBiprodZero (isZero_zero C)).symm, ?_, ?_⟩
  · apply Iso.ext
    dsimp [RawHom.comp, RawHom.id, stabilizerIso]
    change
      biprod.map (isoBiprodZero (isZero_zero C)).symm.hom (𝟙 X.fst) ≫
          f.hom₁.hom =
        (biprod.associator f.stabilizer (0 : C) X.fst).hom ≫
          biprod.map (𝟙 f.stabilizer)
            (isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.hom₁.hom
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ f.hom₁.hom) (rawId_comp_hom f.stabilizer X.fst)
  · apply Iso.ext
    dsimp [RawHom.comp, RawHom.id, stabilizerIso]
    change
      biprod.map (isoBiprodZero (isZero_zero C)).symm.hom (𝟙 X.snd) ≫
          f.hom₂.hom =
        (biprod.associator f.stabilizer (0 : C) X.snd).hom ≫
          biprod.map (𝟙 f.stabilizer)
            (isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.hom₂.hom
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ f.hom₂.hom) (rawId_comp_hom f.stabilizer X.snd)

private theorem rawComp_id_core (s X : C) :
    biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom (𝟙 X) =
      (biprod.associator (0 : C) s X).hom ≫
        (biprod.snd : (0 : C) ⊞ (s ⊞ X) ⟶ s ⊞ X) := by
  apply biprod.hom_ext <;> simp

/-- Coherence between swapping a zero stabilizer to the left and the two
unit orientations used by raw composition. -/
theorem swapZeroUnitCoherence (s X : C) :
    biprod.map (biprod.braiding s (0 : C)).hom (𝟙 X) ≫
          (biprod.associator (0 : C) s X).hom ≫
          (biprod.snd : (0 : C) ⊞ (s ⊞ X) ⟶ s ⊞ X) =
      (biprod.associator s (0 : C) X).hom ≫
        biprod.map (𝟙 s)
          (isoZeroBiprod (isZero_zero C)).symm.hom := by
  apply biprod.hom_ext <;> simp

/-- One-coordinate right-unit coherence for a stabilized morphism. -/
theorem rawComp_id_hom {s X Y : C} (f : s ⊞ X ⟶ Y) :
    biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom (𝟙 X) ≫ f =
      (biprod.associator (0 : C) s X).hom ≫
        biprod.map (𝟙 (0 : C)) f ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom := by
  rw [rawComp_id_core]
  rw [show (isoZeroBiprod (isZero_zero C)).symm.hom =
      (biprod.snd : (0 : C) ⊞ Y ⟶ Y) from rfl,
    biprod.map_snd, Category.assoc]

/-- Right identity holds up to change of stabilizer. -/
theorem RawHom.comp_id_rel {X Y : Pair C} (f : RawHom X Y) :
    f.comp (RawHom.id Y) |>.Rel f := by
  refine ⟨(isoZeroBiprod (isZero_zero C)).symm, ?_, ?_⟩
  · apply Iso.ext
    dsimp [RawHom.comp, RawHom.id, stabilizerIso]
    exact rawComp_id_hom f.hom₁.hom
  · apply Iso.ext
    dsimp [RawHom.comp, RawHom.id, stabilizerIso]
    exact rawComp_id_hom f.hom₂.hom

omit [HasZeroObject C] in
private theorem biprod_associator_pentagon_inv
    (a b c W : C) :
    biprod.map (biprod.associator c b a).inv (𝟙 W) ≫
          (biprod.associator (c ⊞ b) a W).hom ≫
          (biprod.associator c b (a ⊞ W)).hom =
      (biprod.associator c (b ⊞ a) W).hom ≫
        biprod.map (𝟙 c) (biprod.associator b a W).hom := by
  cat_disch

omit [HasZeroObject C] in
/-- One-coordinate associativity coherence for three stabilized
morphisms. -/
theorem rawComp_assoc_hom
    {a b c W X Y Z : C} (f : a ⊞ W ⟶ X)
    (g : b ⊞ X ⟶ Y) (h : c ⊞ Y ⟶ Z) :
    biprod.map (biprod.associator c b a).inv (𝟙 W) ≫
          (biprod.associator (c ⊞ b) a W).hom ≫
          biprod.map (𝟙 (c ⊞ b)) f ≫
          (biprod.associator c b X).hom ≫
          biprod.map (𝟙 c) g ≫ h =
      (biprod.associator c (b ⊞ a) W).hom ≫
          biprod.map (𝟙 c)
            ((biprod.associator b a W).hom ≫
              biprod.map (𝟙 b) f ≫ g) ≫ h := by
  have hid : biprod.map (𝟙 c) (𝟙 b) = 𝟙 (c ⊞ b) := by
    ext <;> simp
  have hnatural :
      biprod.map (𝟙 (c ⊞ b)) f ≫
          (biprod.associator c b X).hom =
        (biprod.associator c b (a ⊞ W)).hom ≫
          biprod.map (𝟙 c) (biprod.map (𝟙 b) f) := by
    rw [← hid]
    exact biprod.associator_natural (𝟙 c) (𝟙 b) f
  have hright :
      biprod.map (𝟙 c)
          ((biprod.associator b a W).hom ≫
            biprod.map (𝟙 b) f ≫ g) =
        biprod.map (𝟙 c) (biprod.associator b a W).hom ≫
          biprod.map (𝟙 c) (biprod.map (𝟙 b) f) ≫
            biprod.map (𝟙 c) g := by
    ext <;> simp
  have hnaturalTail :
      biprod.map (𝟙 (c ⊞ b)) f ≫
          (biprod.associator c b X).hom ≫
          biprod.map (𝟙 c) g ≫ h =
        (biprod.associator c b (a ⊞ W)).hom ≫
          biprod.map (𝟙 c) (biprod.map (𝟙 b) f) ≫
          biprod.map (𝟙 c) g ≫ h := by
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ biprod.map (𝟙 c) g ≫ h) hnatural
  have hpentagonTail :
      biprod.map (biprod.associator c b a).inv (𝟙 W) ≫
          (biprod.associator (c ⊞ b) a W).hom ≫
          (biprod.associator c b (a ⊞ W)).hom ≫
          biprod.map (𝟙 c) (biprod.map (𝟙 b) f) ≫
          biprod.map (𝟙 c) g ≫ h =
        (biprod.associator c (b ⊞ a) W).hom ≫
          biprod.map (𝟙 c) (biprod.associator b a W).hom ≫
          biprod.map (𝟙 c) (biprod.map (𝟙 b) f) ≫
          biprod.map (𝟙 c) g ≫ h := by
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ biprod.map (𝟙 c) (biprod.map (𝟙 b) f) ≫
        biprod.map (𝟙 c) g ≫ h)
      (biprod_associator_pentagon_inv a b c W)
  have hrightTail :
      (biprod.associator c (b ⊞ a) W).hom ≫
          biprod.map (𝟙 c)
            ((biprod.associator b a W).hom ≫
              biprod.map (𝟙 b) f ≫ g) ≫ h =
        (biprod.associator c (b ⊞ a) W).hom ≫
          biprod.map (𝟙 c) (biprod.associator b a W).hom ≫
          biprod.map (𝟙 c) (biprod.map (𝟙 b) f) ≫
          biprod.map (𝟙 c) g ≫ h := by
    simpa only [Category.assoc] using congrArg
      (fun k => (biprod.associator c (b ⊞ a) W).hom ≫ k ≫ h) hright
  rw [hnaturalTail, hpentagonTail]
  exact hrightTail.symm

omit [HasZeroObject C] in
/-- Raw composition is associative modulo the stabilizer relation. -/
theorem RawHom.comp_assoc_rel {W X Y Z : Pair C}
    (f : RawHom W X) (g : RawHom X Y) (h : RawHom Y Z) :
    ((f.comp g).comp h).Rel (f.comp (g.comp h)) := by
  refine ⟨(biprod.associator h.stabilizer g.stabilizer f.stabilizer).symm,
    ?_, ?_⟩
  · apply Iso.ext
    dsimp [RawHom.comp, stabilizerIso]
    exact rawComp_assoc_hom f.hom₁.hom g.hom₁.hom h.hom₁.hom
  · apply Iso.ext
    dsimp [RawHom.comp, stabilizerIso]
    exact rawComp_assoc_hom f.hom₂.hom g.hom₂.hom h.hom₂.hom

/-- The identity quotient arrow. -/
noncomputable def Hom.id (X : Pair C) : Hom X X :=
  Hom.mk (RawHom.id X)

@[simp]
theorem Hom.id_comp {X Y : Pair C} (f : Hom X Y) :
    Hom.comp (Hom.id X) f = f := by
  induction f using Quotient.inductionOn
  apply Quotient.sound
  exact RawHom.id_comp_rel _

@[simp]
theorem Hom.comp_id {X Y : Pair C} (f : Hom X Y) :
    Hom.comp f (Hom.id Y) = f := by
  induction f using Quotient.inductionOn
  apply Quotient.sound
  exact RawHom.comp_id_rel _

omit [HasZeroObject C] in
theorem Hom.comp_assoc {W X Y Z : Pair C}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  induction h using Quotient.inductionOn
  apply Quotient.sound
  exact RawHom.comp_assoc_rel _ _ _

/-- The additive `S⁻¹S` category: objects are pairs and morphisms are
stabilized isomorphism pairs modulo change of stabilizer. -/
noncomputable instance pairCategory : Category.{max v u} (Pair C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-! ## Canonical inclusions -/

/-- Forget a pair of core objects to an object of the additive `S⁻¹S`
category. -/
abbrev Pair.ofCorePair (X : Core C × Core C) : Pair C :=
  ⟨X.1.of, X.2.of⟩

/-- A pair of isomorphisms gives a raw zero-stabilized arrow. -/
noncomputable abbrev RawHom.ofCorePair {X Y : Core C × Core C}
    (f : X ⟶ Y) : RawHom (Pair.ofCorePair X) (Pair.ofCorePair Y) where
  stabilizer := 0
  hom₁ := (isoZeroBiprod (isZero_zero C)).symm.trans f.1.iso
  hom₂ := (isoZeroBiprod (isZero_zero C)).symm.trans f.2.iso

theorem rawOfCorePair_id_rel (X : Core C × Core C) :
    (RawHom.ofCorePair (𝟙 X)).Rel (RawHom.id (Pair.ofCorePair X)) := by
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · dsimp only [RawHom.ofCorePair, RawHom.id, Pair.ofCorePair]
    rw [stabilizerIso_refl, Iso.refl_trans]
    change (isoZeroBiprod (isZero_zero C)).symm =
      (isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl X.1.of)
    exact (Iso.trans_refl _).symm
  · dsimp only [RawHom.ofCorePair, RawHom.id, Pair.ofCorePair]
    rw [stabilizerIso_refl, Iso.refl_trans]
    change (isoZeroBiprod (isZero_zero C)).symm =
      (isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl X.2.of)
    exact (Iso.trans_refl _).symm

theorem rawOfCorePair_comp_rel
    {X Y Z : Core C × Core C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((RawHom.ofCorePair f).comp (RawHom.ofCorePair g)).Rel
      (RawHom.ofCorePair (f ≫ g)) := by
  refine ⟨(isoZeroBiprod (isZero_zero C)).symm, ?_, ?_⟩
  · apply Iso.ext
    dsimp only [RawHom.comp, RawHom.ofCorePair, stabilizerIso,
      Iso.trans_hom, coreCategory_comp_iso]
    change
      biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom (𝟙 X.1.of) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          f.1.iso.hom ≫ g.1.iso.hom =
        (biprod.associator (0 : C) (0 : C) X.1.of).hom ≫
          biprod.map (𝟙 (0 : C))
            ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.1.iso.hom) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫ g.1.iso.hom
    have hunit := rawComp_id_hom
      ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.1.iso.hom)
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ g.1.iso.hom) hunit
  · apply Iso.ext
    dsimp only [RawHom.comp, RawHom.ofCorePair, stabilizerIso,
      Iso.trans_hom, coreCategory_comp_iso]
    change
      biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom (𝟙 X.2.of) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          f.2.iso.hom ≫ g.2.iso.hom =
        (biprod.associator (0 : C) (0 : C) X.2.of).hom ≫
          biprod.map (𝟙 (0 : C))
            ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.2.iso.hom) ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫ g.2.iso.hom
    have hunit := rawComp_id_hom
      ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.2.iso.hom)
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ g.2.iso.hom) hunit

/-- The canonical functor `Core(C) × Core(C) ⟶ S⁻¹S`. -/
noncomputable abbrev corePairInclusion : Core C × Core C ⥤ Pair C where
  obj := Pair.ofCorePair
  map f := Hom.mk (RawHom.ofCorePair f)
  map_id X := Quotient.sound (rawOfCorePair_id_rel X)
  map_comp f g := (Quotient.sound (rawOfCorePair_comp_rel f g)).symm

/-- Pair a core object with the zero core object. -/
noncomputable def coreZeroPair : Core C ⥤ Core C × Core C where
  obj X := (X, ⟨0⟩)
  map f := (f, 𝟙 _)
  map_id X := by
    apply Prod.ext <;> rfl
  map_comp f g := by
    apply Prod.ext
    · rfl
    · simp

/-- The canonical one-sided functor `Core(C) ⟶ S⁻¹S`, sending `X` to
`(X,0)`. -/
noncomputable def coreInclusion : Core C ⥤ Pair C :=
  coreZeroPair ⋙ corePairInclusion

end Zero

end SInverseS
end CategoryTheory
