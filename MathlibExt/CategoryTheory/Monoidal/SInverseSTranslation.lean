/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS

/-!
# The one-coordinate translation category for additive S⁻¹S

For an additive category `C`, the translation category has objects of `C`
and a morphism from `X` to `Y` represented by an object `s` and an
isomorphism `s ⊞ X ≅ Y`, modulo isomorphism of `s`.  This is Weibel's
`⟨S,S⟩` for `S = Core(C)`.

The two-coordinate additive `S⁻¹S` category projects to this category by
forgetting the second coordinate and its stabilized isomorphism.  The zero
object is initial in the translation category.

No homology, cofibered-category, group-completion, or plus-construction
claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Object wrapper for the one-coordinate translation category. -/
structure Translation (C : Type u) where
  /-- The underlying object. -/
  of : C

namespace Translation

/-- A raw translation arrow from `X` to `Y`. -/
structure RawHom (X Y : Translation C) where
  /-- The translating object. -/
  stabilizer : C
  /-- The stabilized isomorphism. -/
  hom : stabilizer ⊞ X.of ≅ Y.of

/-- Change-of-stabilizer relation on raw translation arrows. -/
def RawHom.Rel {X Y : Translation C} (f g : RawHom X Y) : Prop :=
  ∃ e : f.stabilizer ≅ g.stabilizer,
    (SInverseS.stabilizerIso e X.of).trans g.hom = f.hom

theorem RawHom.Rel.refl {X Y : Translation C} (f : RawHom X Y) :
    f.Rel f := by
  refine ⟨Iso.refl f.stabilizer, ?_⟩
  rw [SInverseS.stabilizerIso_refl, Iso.refl_trans]

theorem RawHom.Rel.symm {X Y : Translation C} {f g : RawHom X Y}
    (h : f.Rel g) : g.Rel f := by
  obtain ⟨e, h⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← h, ← Iso.trans_assoc, SInverseS.stabilizerIso_trans]
  simp

theorem RawHom.Rel.trans {X Y : Translation C} {f g h : RawHom X Y}
    (hfg : f.Rel g) (hgh : g.Rel h) : f.Rel h := by
  obtain ⟨e, hfg⟩ := hfg
  obtain ⟨d, hgh⟩ := hgh
  refine ⟨e.trans d, ?_⟩
  rw [← SInverseS.stabilizerIso_trans, Iso.trans_assoc, hgh, hfg]

/-- Setoid of raw translation arrows modulo change of stabilizer. -/
noncomputable instance rawHomSetoid (X Y : Translation C) :
    Setoid (RawHom X Y) where
  r := RawHom.Rel
  iseqv := ⟨RawHom.Rel.refl, RawHom.Rel.symm, RawHom.Rel.trans⟩

/-- Translation arrows modulo change of stabilizer. -/
abbrev Hom (X Y : Translation C) := Quotient (rawHomSetoid X Y)

/-- Insert a raw translation arrow into the quotient. -/
def Hom.mk {X Y : Translation C} (f : RawHom X Y) : Hom X Y :=
  Quotient.mk _ f

/-- Raw composition of translation arrows. -/
noncomputable abbrev RawHom.comp {X Y Z : Translation C}
    (f : RawHom X Y) (g : RawHom Y Z) : RawHom X Z where
  stabilizer := g.stabilizer ⊞ f.stabilizer
  hom := (biprod.associator g.stabilizer f.stabilizer X.of).trans
    ((biprod.mapIso (Iso.refl g.stabilizer) f.hom).trans g.hom)

/-- Raw composition respects change of stabilizer. -/
theorem RawHom.comp_rel {X Y Z : Translation C}
    {f f' : RawHom X Y} {g g' : RawHom Y Z}
    (hf : f.Rel f') (hg : g.Rel g') :
    (f.comp g).Rel (f'.comp g') := by
  obtain ⟨ef, hf⟩ := hf
  obtain ⟨eg, hg⟩ := hg
  refine ⟨biprod.mapIso eg ef, ?_⟩
  dsimp only [RawHom.comp]
  rw [← hf, ← hg]
  apply Iso.ext
  dsimp [SInverseS.stabilizerIso]
  exact SInverseS.rawComp_changeStabilizer_hom ef.hom eg.hom
    f'.hom.hom g'.hom.hom

/-- Composition on quotient translation arrows. -/
noncomputable def Hom.comp {X Y Z : Translation C}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.map₂ RawHom.comp
    (fun _ _ hf _ _ hg => RawHom.comp_rel hf hg) f g

section Zero

variable [HasZeroObject C]

/-- The wrapped zero object. -/
noncomputable instance : Zero (Translation C) :=
  ⟨⟨0⟩⟩

/-- Raw identity arrow. -/
noncomputable def RawHom.id (X : Translation C) : RawHom X X where
  stabilizer := 0
  hom := (isoZeroBiprod (isZero_zero C)).symm

theorem RawHom.id_comp_rel {X Y : Translation C} (f : RawHom X Y) :
    (RawHom.id X).comp f |>.Rel f := by
  refine ⟨(isoBiprodZero (isZero_zero C)).symm, ?_⟩
  apply Iso.ext
  dsimp [RawHom.comp, RawHom.id, SInverseS.stabilizerIso]
  change
    biprod.map (isoBiprodZero (isZero_zero C)).symm.hom
          (𝟙 X.of) ≫ f.hom.hom =
      (biprod.associator f.stabilizer (0 : C) X.of).hom ≫
        biprod.map (𝟙 f.stabilizer)
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫ f.hom.hom
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ f.hom.hom)
    (SInverseS.rawId_comp_hom f.stabilizer X.of)

theorem RawHom.comp_id_rel {X Y : Translation C} (f : RawHom X Y) :
    f.comp (RawHom.id Y) |>.Rel f := by
  refine ⟨(isoZeroBiprod (isZero_zero C)).symm, ?_⟩
  apply Iso.ext
  dsimp [RawHom.comp, RawHom.id, SInverseS.stabilizerIso]
  exact SInverseS.rawComp_id_hom f.hom.hom

omit [HasZeroObject C] in
theorem RawHom.comp_assoc_rel {W X Y Z : Translation C}
    (f : RawHom W X) (g : RawHom X Y) (h : RawHom Y Z) :
    ((f.comp g).comp h).Rel (f.comp (g.comp h)) := by
  refine ⟨(biprod.associator h.stabilizer g.stabilizer
    f.stabilizer).symm, ?_⟩
  apply Iso.ext
  dsimp [RawHom.comp, SInverseS.stabilizerIso]
  exact SInverseS.rawComp_assoc_hom
    f.hom.hom g.hom.hom h.hom.hom

/-- Quotient identity arrow. -/
noncomputable def Hom.id (X : Translation C) : Hom X X :=
  Hom.mk (RawHom.id X)

@[simp]
theorem Hom.id_comp {X Y : Translation C} (f : Hom X Y) :
    Hom.comp (Hom.id X) f = f := by
  induction f using Quotient.inductionOn
  apply Quotient.sound
  exact RawHom.id_comp_rel _

@[simp]
theorem Hom.comp_id {X Y : Translation C} (f : Hom X Y) :
    Hom.comp f (Hom.id Y) = f := by
  induction f using Quotient.inductionOn
  apply Quotient.sound
  exact RawHom.comp_id_rel _

omit [HasZeroObject C] in
theorem Hom.comp_assoc {W X Y Z : Translation C}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  induction h using Quotient.inductionOn
  apply Quotient.sound
  exact RawHom.comp_assoc_rel _ _ _

/-- Category structure on the one-coordinate translation category. -/
noncomputable instance category : Category.{max v u} (Translation C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- Canonical raw arrow from zero to an object. -/
noncomputable def RawHom.fromZero (X : Translation C) :
    RawHom (0 : Translation C) X where
  stabilizer := X.of
  hom := (isoBiprodZero (isZero_zero C)).symm

/-- Canonical arrow from zero to an object. -/
noncomputable def fromZero (X : Translation C) :
    (0 : Translation C) ⟶ X :=
  Hom.mk (RawHom.fromZero X)

/-- Every arrow from zero is the canonical one. -/
theorem hom_fromZero_unique (X : Translation C)
    (f : (0 : Translation C) ⟶ X) : f = fromZero X := by
  induction f using Quotient.inductionOn with
  | _ f =>
      apply Quotient.sound
      let e : f.stabilizer ≅ X.of :=
        (isoBiprodZero (isZero_zero C)).trans f.hom
      refine ⟨e, ?_⟩
      apply Iso.ext
      dsimp only [RawHom.fromZero, SInverseS.stabilizerIso]
      apply biprod.hom_ext'
      · change
          (biprod.inl : f.stabilizer ⟶
              f.stabilizer ⊞ (0 : C)) ≫
                biprod.map e.hom (𝟙 (0 : C)) ≫
                (isoBiprodZero (isZero_zero C)).symm.hom =
            (biprod.inl : f.stabilizer ⟶
              f.stabilizer ⊞ (0 : C)) ≫ f.hom.hom
        rw [← Category.assoc, biprod.inl_map]
        simp [e, Category.assoc]
      · exact (isZero_zero C).eq_of_src _ _

/-- The wrapped zero object is initial. -/
noncomputable def zeroIsInitial : IsInitial (0 : Translation C) :=
  IsInitial.ofUniqueHom
    (fun X => fromZero X)
    (fun X f => hom_fromZero_unique X f)

end Zero

end Translation

section Projection

variable [HasZeroObject C]

/-- Forget the second coordinate of a raw `S⁻¹S` arrow. -/
noncomputable def RawHom.toTranslation {X Y : Pair C}
    (f : RawHom X Y) :
    Translation.RawHom ⟨X.fst⟩ ⟨Y.fst⟩ where
  stabilizer := f.stabilizer
  hom := f.hom₁

omit [HasZeroObject C] in
theorem RawHom.toTranslation_rel {X Y : Pair C}
    {f g : RawHom X Y} (h : f.Rel g) :
    (f.toTranslation).Rel (g.toTranslation) := by
  obtain ⟨e, h₁, _⟩ := h
  exact ⟨e, h₁⟩

/-- Forget the second coordinate of a quotient `S⁻¹S` arrow. -/
noncomputable def Hom.toTranslation {X Y : Pair C} (f : Hom X Y) :
    Translation.Hom ⟨X.fst⟩ ⟨Y.fst⟩ :=
  Quotient.map RawHom.toTranslation
    (fun _ _ h => RawHom.toTranslation_rel h) f

/-- Projection from additive `S⁻¹S` to the one-coordinate translation
category. -/
noncomputable def translationProjection : Pair C ⥤ Translation C where
  obj X := ⟨X.fst⟩
  map := Hom.toTranslation
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl

@[simp]
theorem translationProjection_obj_of (X : Pair C) :
    (translationProjection (C := C)).obj X = ⟨X.fst⟩ :=
  rfl

end Projection

end SInverseS
end CategoryTheory

end
