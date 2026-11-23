/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Residual translations on additive S⁻¹S

Fixing an object `A`, one can add `A` to either coordinate of an additive
`S⁻¹S` pair.  On a stabilized arrow, the stabilizer is commuted past `A`
before applying the original coordinate isomorphism.

The two operations are packaged as endofunctors.  Diagonal addition gives
natural transformations from the identity to both composites, so the
induced nerve maps are simplicial homotopy inverses via the existing nerve
homotopy construction.  No separate realization-homotopy mechanism or
homology-localization claim is introduced here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Commute a stabilizer past a fixed left biproduct summand. -/
noncomputable def swapStabilizerIso (A s X : C) :
    s ⊞ (A ⊞ X) ≅ A ⊞ (s ⊞ X) :=
  (biprod.associator s A X).symm.trans
    ((biprod.mapIso (biprod.braiding s A) (Iso.refl X)).trans
      (biprod.associator A s X))

omit [HasZeroObject C] in
/-- The stabilizer summand is sent to the middle summand by the swap. -/
@[reassoc (attr := simp)]
theorem inl_swapStabilizerIso_hom (A s X : C) :
    (biprod.inl : s ⟶ s ⊞ (A ⊞ X)) ≫
        (swapStabilizerIso A s X).hom =
      (biprod.inl : s ⟶ s ⊞ X) ≫
        (biprod.inr : s ⊞ X ⟶ A ⊞ (s ⊞ X)) := by
  apply biprod.hom_ext
  · simp [swapStabilizerIso, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [swapStabilizerIso, Category.assoc]

omit [HasZeroObject C] in
/-- The fixed summand is sent to the first summand by the swap. -/
@[reassoc (attr := simp)]
theorem inl_inr_swapStabilizerIso_hom (A s X : C) :
    (biprod.inl : A ⟶ A ⊞ X) ≫
        (biprod.inr : A ⊞ X ⟶ s ⊞ (A ⊞ X)) ≫
        (swapStabilizerIso A s X).hom =
      (biprod.inl : A ⟶ A ⊞ (s ⊞ X)) := by
  apply biprod.hom_ext
  · simp [swapStabilizerIso, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [swapStabilizerIso, Category.assoc]

omit [HasZeroObject C] in
/-- The final summand remains the final summand under the swap. -/
@[reassoc (attr := simp)]
theorem inr_inr_swapStabilizerIso_hom (A s X : C) :
    (biprod.inr : X ⟶ A ⊞ X) ≫
        (biprod.inr : A ⊞ X ⟶ s ⊞ (A ⊞ X)) ≫
        (swapStabilizerIso A s X).hom =
      (biprod.inr : X ⟶ s ⊞ X) ≫
        (biprod.inr : s ⊞ X ⟶ A ⊞ (s ⊞ X)) := by
  apply biprod.hom_ext
  · simp [swapStabilizerIso, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [swapStabilizerIso, Category.assoc]

omit [HasZeroObject C] in
/-- The swap-associator is natural under change of stabilizer. -/
theorem stabilizerIso_trans_swapStabilizerIso
    (A X : C) {s t : C} (e : s ≅ t) :
    (stabilizerIso e (A ⊞ X)).trans (swapStabilizerIso A t X) =
      (swapStabilizerIso A s X).trans
        (biprod.mapIso (Iso.refl A) (stabilizerIso e X)) := by
  apply Iso.ext
  ext <;> simp [swapStabilizerIso, stabilizerIso, Category.assoc]

omit [HasZeroObject C] in
/-- Mapping a composite in the second biproduct coordinate with the first
coordinate fixed at the identity. -/
theorem biprodMap_id_comp (A : C) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    biprod.map (𝟙 A) (f ≫ g) =
      biprod.map (𝟙 A) f ≫ biprod.map (𝟙 A) g := by
  ext <;> simp

omit [HasZeroObject C] in
/-- Naturality of the swap-associator in its final coordinate. -/
@[reassoc]
theorem swapStabilizerIso_natural_hom
    (A s : C) {X Y : C} (f : X ⟶ Y) :
    biprod.map (𝟙 s) (biprod.map (𝟙 A) f) ≫
        (swapStabilizerIso A s Y).hom =
      (swapStabilizerIso A s X).hom ≫
        biprod.map (𝟙 A) (biprod.map (𝟙 s) f) := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [HasZeroObject C] in
/-- The first summand under the biproduct associator. -/
@[reassoc (attr := simp)]
theorem inl_inl_associator_hom (t s X : C) :
    (biprod.inl : t ⟶ t ⊞ s) ≫
        (biprod.inl : t ⊞ s ⟶ (t ⊞ s) ⊞ X) ≫
        (biprod.associator t s X).hom =
      (biprod.inl : t ⟶ t ⊞ (s ⊞ X)) := by
  apply biprod.hom_ext
  · simp [biprod.associator, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [biprod.associator, Category.assoc]

omit [HasZeroObject C] in
/-- The middle summand under the biproduct associator. -/
@[reassoc (attr := simp)]
theorem inr_inl_associator_hom (t s X : C) :
    (biprod.inr : s ⟶ t ⊞ s) ≫
        (biprod.inl : t ⊞ s ⟶ (t ⊞ s) ⊞ X) ≫
        (biprod.associator t s X).hom =
      (biprod.inl : s ⟶ s ⊞ X) ≫
        (biprod.inr : s ⊞ X ⟶ t ⊞ (s ⊞ X)) := by
  apply biprod.hom_ext
  · simp [biprod.associator, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [biprod.associator, Category.assoc]

omit [HasZeroObject C] in
/-- The final summand under the biproduct associator. -/
@[reassoc (attr := simp)]
theorem inr_associator_hom (t s X : C) :
    (biprod.inr : X ⟶ (t ⊞ s) ⊞ X) ≫
        (biprod.associator t s X).hom =
      (biprod.inr : X ⟶ s ⊞ X) ≫
        (biprod.inr : s ⊞ X ⟶ t ⊞ (s ⊞ X)) := by
  apply biprod.hom_ext
  · simp [biprod.associator, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [biprod.associator, Category.assoc]

omit [HasZeroObject C] in
/-- Hexagon coherence for commuting a composite stabilizer past a fixed
summand. -/
@[reassoc]
theorem swapStabilizerIso_hexagon_hom (A t s X : C) :
    (biprod.associator t s (A ⊞ X)).hom ≫
          biprod.map (𝟙 t) (swapStabilizerIso A s X).hom ≫
          (swapStabilizerIso A t (s ⊞ X)).hom =
      (swapStabilizerIso A (t ⊞ s) X).hom ≫
        biprod.map (𝟙 A) (biprod.associator t s X).hom := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext'
    · simp only [inl_inl_associator_hom_assoc,
        biprod.inl_map_assoc, inl_swapStabilizerIso_hom_assoc]
      slice_lhs 1 2 => rw [Category.id_comp]
      slice_lhs 1 2 => rw [inl_swapStabilizerIso_hom]
      slice_rhs 3 4 => rw [biprod.inr_map]
      slice_rhs 1 3 => rw [inl_inl_associator_hom]
    · simp only [inr_inl_associator_hom_assoc]
      slice_lhs 2 3 => rw [biprod.inr_map]
      slice_lhs 1 2 => rw [inl_swapStabilizerIso_hom]
      slice_lhs 2 4 => rw [inr_inr_swapStabilizerIso_hom]
      slice_rhs 2 3 => rw [inl_swapStabilizerIso_hom]
      slice_rhs 3 4 => rw [biprod.inr_map]
      slice_rhs 1 3 => rw [inr_inl_associator_hom]
      simp only [Category.assoc]
  · apply biprod.hom_ext'
    · simp only [inr_associator_hom_assoc,
        biprod.inr_map_assoc, inl_inr_swapStabilizerIso_hom_assoc]
      rw [inl_inr_swapStabilizerIso_hom, biprod.inl_map,
        Category.id_comp]
    · simp only [inr_associator_hom_assoc,
        biprod.inr_map_assoc, inr_inr_swapStabilizerIso_hom_assoc]
      slice_lhs 2 4 => rw [inr_inr_swapStabilizerIso_hom]
      slice_rhs 2 3 => rw [biprod.inr_map]
      slice_rhs 1 2 => rw [inr_associator_hom]
      simp only [Category.assoc]

omit [HasZeroObject C] in
/-- Coordinate coherence for diagonal addition followed by translation. -/
theorem diagonalAddCoordinateIso (A s X Y : C) (f : s ⊞ X ≅ Y) :
    (stabilizerIso (biprod.braiding s A) X).trans
        ((biprod.associator A s X).trans
          ((biprod.mapIso (Iso.refl A) f).trans (Iso.refl _))) =
      (biprod.associator s A X).trans
        ((biprod.mapIso (Iso.refl s) (Iso.refl (A ⊞ X))).trans
          ((swapStabilizerIso A s X).trans
            (biprod.mapIso (Iso.refl A) f))) := by
  have hid : biprod.mapIso (Iso.refl s) (Iso.refl (A ⊞ X)) =
      Iso.refl (s ⊞ (A ⊞ X)) := by
    apply Iso.ext
    ext <;> simp
  rw [hid, Iso.refl_trans, Iso.trans_refl]
  apply Iso.ext
  simp [swapStabilizerIso, stabilizerIso]

/-- Add `A` to the first coordinate of a pair. -/
abbrev translateFirstObj (A : C) (X : Pair C) : Pair C :=
  ⟨A ⊞ X.fst, X.snd⟩

/-- Add `A` to the second coordinate of a pair. -/
abbrev translateSecondObj (A : C) (X : Pair C) : Pair C :=
  ⟨X.fst, A ⊞ X.snd⟩

namespace RawHom

/-- Translate the first coordinate of a raw stabilized arrow. -/
noncomputable def translateFirst (A : C) {X Y : Pair C}
    (f : RawHom X Y) :
    RawHom (translateFirstObj A X) (translateFirstObj A Y) where
  stabilizer := f.stabilizer
  hom₁ := (swapStabilizerIso A f.stabilizer X.fst).trans
    (biprod.mapIso (Iso.refl A) f.hom₁)
  hom₂ := f.hom₂

/-- Translate the second coordinate of a raw stabilized arrow. -/
noncomputable def translateSecond (A : C) {X Y : Pair C}
    (f : RawHom X Y) :
    RawHom (translateSecondObj A X) (translateSecondObj A Y) where
  stabilizer := f.stabilizer
  hom₁ := f.hom₁
  hom₂ := (swapStabilizerIso A f.stabilizer X.snd).trans
    (biprod.mapIso (Iso.refl A) f.hom₂)

omit [HasZeroObject C] in
/-- First-coordinate translation respects change of stabilizer. -/
theorem translateFirst_rel (A : C) {X Y : Pair C}
    {f g : RawHom X Y} (h : f.Rel g) :
    (f.translateFirst A).Rel (g.translateFirst A) := by
  obtain ⟨e, h₁, h₂⟩ := h
  refine ⟨e, ?_, h₂⟩
  change (stabilizerIso e (A ⊞ X.fst)).trans
      ((swapStabilizerIso A g.stabilizer X.fst).trans
        (biprod.mapIso (Iso.refl A) g.hom₁)) =
    (swapStabilizerIso A f.stabilizer X.fst).trans
      (biprod.mapIso (Iso.refl A) f.hom₁)
  rw [← h₁]
  rw [← Iso.trans_assoc,
    stabilizerIso_trans_swapStabilizerIso,
    Iso.trans_assoc]
  apply Iso.ext
  ext <;> simp [stabilizerIso, Category.assoc]

omit [HasZeroObject C] in
/-- Second-coordinate translation respects change of stabilizer. -/
theorem translateSecond_rel (A : C) {X Y : Pair C}
    {f g : RawHom X Y} (h : f.Rel g) :
    (f.translateSecond A).Rel (g.translateSecond A) := by
  obtain ⟨e, h₁, h₂⟩ := h
  refine ⟨e, h₁, ?_⟩
  change (stabilizerIso e (A ⊞ X.snd)).trans
      ((swapStabilizerIso A g.stabilizer X.snd).trans
        (biprod.mapIso (Iso.refl A) g.hom₂)) =
    (swapStabilizerIso A f.stabilizer X.snd).trans
      (biprod.mapIso (Iso.refl A) f.hom₂)
  rw [← h₂]
  rw [← Iso.trans_assoc,
    stabilizerIso_trans_swapStabilizerIso,
    Iso.trans_assoc]
  apply Iso.ext
  ext <;> simp [stabilizerIso, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- First-coordinate translation preserves the raw identity modulo change
of stabilizer. -/
theorem translateFirst_id_rel (A : C) (X : Pair C) :
    (RawHom.id X).translateFirst A |>.Rel
      (RawHom.id (translateFirstObj A X)) := by
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · apply Iso.ext
    ext <;> simp [translateFirst, RawHom.id, swapStabilizerIso,
      stabilizerIso, Category.assoc]
  · apply Iso.ext
    ext <;> simp [translateFirst, RawHom.id, stabilizerIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Second-coordinate translation preserves the raw identity modulo change
of stabilizer. -/
theorem translateSecond_id_rel (A : C) (X : Pair C) :
    (RawHom.id X).translateSecond A |>.Rel
      (RawHom.id (translateSecondObj A X)) := by
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · apply Iso.ext
    ext <;> simp [translateSecond, RawHom.id, stabilizerIso]
  · apply Iso.ext
    ext <;> simp [translateSecond, RawHom.id, swapStabilizerIso,
      stabilizerIso, Category.assoc]

omit [HasZeroObject C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- First-coordinate translation preserves raw composition modulo change of
stabilizer. -/
theorem translateFirst_comp_rel (A : C) {X Y Z : Pair C}
    (f : RawHom X Y) (g : RawHom Y Z) :
    (f.comp g).translateFirst A |>.Rel
      ((f.translateFirst A).comp (g.translateFirst A)) := by
  refine ⟨Iso.refl (g.stabilizer ⊞ f.stabilizer), ?_, ?_⟩
  · change
      (stabilizerIso (Iso.refl (g.stabilizer ⊞ f.stabilizer))
          (A ⊞ X.fst)).trans
          ((f.translateFirst A).comp (g.translateFirst A)).hom₁ =
        ((f.comp g).translateFirst A).hom₁
    rw [stabilizerIso_refl, Iso.refl_trans]
    apply Iso.ext
    change
      (biprod.associator g.stabilizer f.stabilizer
            (A ⊞ X.fst)).hom ≫
          biprod.map (𝟙 g.stabilizer)
            ((swapStabilizerIso A f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 A) f.hom₁.hom) ≫
          (swapStabilizerIso A g.stabilizer Y.fst).hom ≫
          biprod.map (𝟙 A) g.hom₁.hom =
        (swapStabilizerIso A (g.stabilizer ⊞ f.stabilizer) X.fst).hom ≫
          biprod.map (𝟙 A)
            ((biprod.associator g.stabilizer f.stabilizer X.fst).hom ≫
              biprod.map (𝟙 g.stabilizer) f.hom₁.hom ≫
              g.hom₁.hom)
    rw [biprodMap_id_comp]
    simp only [Category.assoc]
    rw [swapStabilizerIso_natural_hom_assoc]
    rw [swapStabilizerIso_hexagon_hom_assoc]
    rw [← biprodMap_id_comp, ← biprodMap_id_comp]
  · apply Iso.ext
    ext <;> simp [translateFirst, RawHom.comp, stabilizerIso]

omit [HasZeroObject C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Second-coordinate translation preserves raw composition modulo change
of stabilizer. -/
  theorem translateSecond_comp_rel (A : C) {X Y Z : Pair C}
    (f : RawHom X Y) (g : RawHom Y Z) :
    (f.comp g).translateSecond A |>.Rel
      ((f.translateSecond A).comp (g.translateSecond A)) := by
  refine ⟨Iso.refl (g.stabilizer ⊞ f.stabilizer), ?_, ?_⟩
  · apply Iso.ext
    ext <;> simp [translateSecond, RawHom.comp, stabilizerIso]
  · change
      (stabilizerIso (Iso.refl (g.stabilizer ⊞ f.stabilizer))
          (A ⊞ X.snd)).trans
          ((f.translateSecond A).comp (g.translateSecond A)).hom₂ =
        ((f.comp g).translateSecond A).hom₂
    rw [stabilizerIso_refl, Iso.refl_trans]
    apply Iso.ext
    change
      (biprod.associator g.stabilizer f.stabilizer
            (A ⊞ X.snd)).hom ≫
          biprod.map (𝟙 g.stabilizer)
            ((swapStabilizerIso A f.stabilizer X.snd).hom ≫
              biprod.map (𝟙 A) f.hom₂.hom) ≫
          (swapStabilizerIso A g.stabilizer Y.snd).hom ≫
          biprod.map (𝟙 A) g.hom₂.hom =
        (swapStabilizerIso A (g.stabilizer ⊞ f.stabilizer) X.snd).hom ≫
          biprod.map (𝟙 A)
            ((biprod.associator g.stabilizer f.stabilizer X.snd).hom ≫
              biprod.map (𝟙 g.stabilizer) f.hom₂.hom ≫
              g.hom₂.hom)
    rw [biprodMap_id_comp]
    simp only [Category.assoc]
    rw [swapStabilizerIso_natural_hom_assoc]
    rw [swapStabilizerIso_hexagon_hom_assoc]
    rw [← biprodMap_id_comp, ← biprodMap_id_comp]

end RawHom

/-- First-coordinate translation on quotient arrows. -/
noncomputable def Hom.translateFirst (A : C) {X Y : Pair C} :
    Hom X Y → Hom (translateFirstObj A X) (translateFirstObj A Y) :=
  Quotient.map (RawHom.translateFirst A)
    (fun _ _ h ↦ RawHom.translateFirst_rel A h)

/-- Second-coordinate translation on quotient arrows. -/
noncomputable def Hom.translateSecond (A : C) {X Y : Pair C} :
    Hom X Y → Hom (translateSecondObj A X) (translateSecondObj A Y) :=
  Quotient.map (RawHom.translateSecond A)
    (fun _ _ h ↦ RawHom.translateSecond_rel A h)

/-- Add a fixed object to the first coordinate of additive `S⁻¹S`. -/
noncomputable def translateFirstFunctor (A : C) : Pair C ⥤ Pair C where
  obj := translateFirstObj A
  map := Hom.translateFirst A
  map_id X := Quotient.sound (RawHom.translateFirst_id_rel A X)
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    exact Quotient.sound (RawHom.translateFirst_comp_rel A _ _)

/-- Add a fixed object to the second coordinate of additive `S⁻¹S`. -/
noncomputable def translateSecondFunctor (A : C) : Pair C ⥤ Pair C where
  obj := translateSecondObj A
  map := Hom.translateSecond A
  map_id X := Quotient.sound (RawHom.translateSecond_id_rel A X)
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    exact Quotient.sound (RawHom.translateSecond_comp_rel A _ _)

/-- Translate second by the selected object's first coordinate and first by
its second coordinate. In a preadditive setting this carries the selected
Grothendieck component to zero. -/
noncomputable def translateToZeroFunctor (X : Pair C) : Pair C ⥤ Pair C :=
  translateSecondFunctor X.fst ⋙ translateFirstFunctor X.snd

namespace RawHom

/-- Add the same stabilizer to both coordinates by identity
isomorphisms. -/
noncomputable def diagonalAdd (A : C) (X : Pair C) :
    RawHom X ⟨A ⊞ X.fst, A ⊞ X.snd⟩ where
  stabilizer := A
  hom₁ := Iso.refl _
  hom₂ := Iso.refl _

omit [HasZeroObject C] in
/-- Translating the two coordinates commutes strictly at the raw-arrow
level. -/
theorem translateFirst_translateSecond (A : C) {X Y : Pair C}
    (f : RawHom X Y) :
    (f.translateFirst A).translateSecond A =
      (f.translateSecond A).translateFirst A :=
  rfl

omit [HasZeroObject C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of diagonal addition before passing to the stabilizer
quotient. -/
theorem diagonalAdd_naturality_rel (A : C) {X Y : Pair C}
    (f : RawHom X Y) :
    ((diagonalAdd A X).comp
        ((f.translateFirst A).translateSecond A)).Rel
      (f.comp (diagonalAdd A Y)) := by
  refine ⟨biprod.braiding f.stabilizer A, ?_, ?_⟩
  · simpa [diagonalAdd, translateFirst, translateSecond,
      RawHom.comp] using diagonalAddCoordinateIso A f.stabilizer
        X.fst Y.fst f.hom₁
  · simpa [diagonalAdd, translateFirst, translateSecond,
      RawHom.comp] using diagonalAddCoordinateIso A f.stabilizer
        X.snd Y.snd f.hom₂

end RawHom

/-- The canonical arrow adding `A` diagonally to both coordinates. -/
noncomputable def diagonalAddHom (A : C) (X : Pair C) :
    X ⟶ ⟨A ⊞ X.fst, A ⊞ X.snd⟩ :=
  Hom.mk (RawHom.diagonalAdd A X)

/-- Diagonal addition is a natural transformation from the identity to
first-coordinate translation followed by second-coordinate translation. -/
noncomputable def diagonalAddFirstSecondNatTrans (A : C) :
    𝟭 (Pair C) ⟶
      (translateFirstFunctor A ⋙ translateSecondFunctor A) where
  app X := diagonalAddHom A X
  naturality {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f =>
        exact (Quotient.sound
          (RawHom.diagonalAdd_naturality_rel A f)).symm

/-- Diagonal addition is also a natural transformation from the identity to
second-coordinate translation followed by first-coordinate translation. -/
noncomputable def diagonalAddSecondFirstNatTrans (A : C) :
    𝟭 (Pair C) ⟶
      (translateSecondFunctor A ⋙ translateFirstFunctor A) where
  app X := diagonalAddHom A X
  naturality {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f =>
        change Hom.mk (f.comp (RawHom.diagonalAdd A Y)) =
          Hom.mk ((RawHom.diagonalAdd A X).comp
            ((f.translateSecond A).translateFirst A))
        rw [← RawHom.translateFirst_translateSecond A f]
        exact (Quotient.sound
          (RawHom.diagonalAdd_naturality_rel A f)).symm

/-- On nerves, first-coordinate and second-coordinate translations compose
to a map simplicially homotopic to the identity. -/
noncomputable def translateFirstSecondNerveHomotopy (A : C) :
    SSet.Homotopy (𝟙 (CategoryTheory.nerve (Pair C)))
      (CategoryTheory.nerveMap (translateFirstFunctor A) ≫
        CategoryTheory.nerveMap (translateSecondFunctor A)) := by
  simpa using CategoryTheory.NatTrans.nerveHomotopy
    (diagonalAddFirstSecondNatTrans A)

/-- In the opposite order, the two coordinate translations again compose
to a map simplicially homotopic to the identity. -/
noncomputable def translateSecondFirstNerveHomotopy (A : C) :
    SSet.Homotopy (𝟙 (CategoryTheory.nerve (Pair C)))
      (CategoryTheory.nerveMap (translateSecondFunctor A) ≫
        CategoryTheory.nerveMap (translateFirstFunctor A)) := by
  simpa using CategoryTheory.NatTrans.nerveHomotopy
    (diagonalAddSecondFirstNatTrans A)

end SInverseS
end CategoryTheory

end
