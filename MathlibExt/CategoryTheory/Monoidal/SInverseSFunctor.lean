/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSwapCoreComparison
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationComponents

/-!
# Additive transport of stabilized pairs

This construction sends the original common stabilizer and both
coordinate isomorphisms through an additive functor. The zero and biproduct
comparisons are the canonical ones. The full projective-model transport,
including its chain and realization comparisons, remains open.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe uC vC uD vD

namespace CategoryTheory.SInverseS

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

private instance preservesBinaryBiproduct (X Y : C) :
    PreservesBinaryBiproduct X Y F :=
  preservesBinaryBiproduct_of_preservesBiproduct F X Y

private def biprodIso (X Y : C) :
    F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  F.mapBiprod X Y

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
@[reassoc (attr := simp)]
private theorem biprodIso_hom_fst (X Y : C) :
    (biprodIso F X Y).hom ≫ biprod.fst = F.map biprod.fst :=
  F.biprodComparison_fst X Y

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
@[reassoc (attr := simp)]
private theorem biprodIso_hom_snd (X Y : C) :
    (biprodIso F X Y).hom ≫ biprod.snd = F.map biprod.snd :=
  F.biprodComparison_snd X Y

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
@[reassoc (attr := simp)]
private theorem inl_biprodIso_inv (X Y : C) :
    biprod.inl ≫ (biprodIso F X Y).inv = F.map biprod.inl := by
  change biprod.inl ≫ (F.mapBiprod X Y).inv = F.map biprod.inl
  rw [Functor.mapBiprod_inv]
  simp

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
@[reassoc (attr := simp)]
private theorem inr_biprodIso_inv (X Y : C) :
    biprod.inr ≫ (biprodIso F X Y).inv = F.map biprod.inr := by
  change biprod.inr ≫ (F.mapBiprod X Y).inv = F.map biprod.inr
  rw [Functor.mapBiprod_inv]
  simp

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem biprodIso_natural {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (biprod.map f g) ≫ (biprodIso F X' Y').hom =
      (biprodIso F X Y).hom ≫ biprod.map (F.map f) (F.map g) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprodIso_hom_fst, Category.assoc, biprod.map_fst,
      ← Category.assoc, biprodIso_hom_fst, ← F.map_comp, biprod.map_fst, F.map_comp]
  · rw [Category.assoc, biprodIso_hom_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc, biprodIso_hom_snd, ← F.map_comp, biprod.map_snd, F.map_comp]

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem biprodIso_inv_natural {X Y X' Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    biprod.map (F.map f) (F.map g) ≫ (biprodIso F X' Y').inv =
      (biprodIso F X Y).inv ≫ F.map (biprod.map f g) := by
  have h := congrArg
    (fun k => (biprodIso F X Y).inv ≫ k ≫ (biprodIso F X' Y').inv)
    (biprodIso_natural F f g)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h.symm

private abbrev zeroUnitC (X : C) : (0 : C) ⊞ X ≅ X :=
  (isoZeroBiprod (isZero_zero C)).symm

private abbrev zeroUnitD (X : D) : (0 : D) ⊞ X ≅ X :=
  (isoZeroBiprod (isZero_zero D)).symm

private theorem biprodIso_zero_unit (X : C) :
    (stabilizerIso F.mapZeroObject (F.obj X)).trans (zeroUnitD (F.obj X)) =
      (biprodIso F (0 : C) X).symm.trans (F.mapIso (zeroUnitC X)) := by
  apply Iso.ext
  apply biprod.hom_ext' <;>
    simp [stabilizerIso, zeroUnitC, zeroUnitD, ← F.map_comp]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem biprodIso_associator (t s X : C) :
    (F.mapIso (biprod.associator t s X)).trans
        ((biprodIso F t (s ⊞ X)).trans
          (biprod.mapIso (Iso.refl (F.obj t)) (biprodIso F s X))) =
      (biprodIso F (t ⊞ s) X).trans
        ((biprod.mapIso (biprodIso F t s) (Iso.refl (F.obj X))).trans
          (biprod.associator (F.obj t) (F.obj s) (F.obj X))) := by
  apply Iso.ext
  simp only [Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom, Functor.mapIso_hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      biprodIso_hom_fst, ← F.map_comp, biprod.associator_hom, biprod.lift_fst]
    rw [biprod.map_fst_assoc, biprodIso_hom_fst,
      biprodIso_hom_fst_assoc, F.map_comp]
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_snd,
        biprodIso_hom_fst, biprod.associator_hom, biprod.lift_snd, biprod.lift_fst]
      rw [biprodIso_hom_snd_assoc, biprod.map_fst_assoc,
        biprodIso_hom_snd, biprodIso_hom_fst_assoc]
      simp only [← F.map_comp, biprod.lift_snd_assoc, biprod.lift_fst]
    · simp only [Category.assoc, biprod.map_snd, Category.comp_id,
        biprodIso_hom_snd, biprod.associator_hom, biprod.lift_snd]
      rw [biprodIso_hom_snd_assoc]
      simp only [← F.map_comp, biprod.lift_snd_assoc, biprod.lift_snd]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem biprodIso_braiding (X Y : C) :
    (F.mapIso (biprod.braiding X Y)).trans (biprodIso F Y X) =
      (biprodIso F X Y).trans (biprod.braiding (F.obj X) (F.obj Y)) := by
  apply Iso.ext
  apply biprod.hom_ext <;> simp [biprod.braiding, ← F.map_comp, Category.assoc]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem biprodIso_associator_inv_hom (t s X : C) :
    biprod.map (biprodIso F t s).hom (𝟙 (F.obj X)) ≫
        (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
        biprod.map (𝟙 (F.obj t)) (biprodIso F s X).inv =
      (biprodIso F (t ⊞ s) X).inv ≫
        F.map (biprod.associator t s X).hom ≫
        (biprodIso F t (s ⊞ X)).hom := by
  have h := congrArg
    (fun k => (biprodIso F (t ⊞ s) X).inv ≫ k ≫
      (biprod.mapIso (Iso.refl (F.obj t)) (biprodIso F s X)).inv)
    (congrArg Iso.hom (biprodIso_associator F t s X))
  have h' :
      (biprod.mapIso (biprodIso F t s) (Iso.refl (F.obj X))).hom ≫
          (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
          (biprod.mapIso (Iso.refl (F.obj t)) (biprodIso F s X)).inv =
        (biprodIso F (t ⊞ s) X).inv ≫
          (F.mapIso (biprod.associator t s X)).hom ≫
          (biprodIso F t (s ⊞ X)).hom := by
    simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using h.symm
  simpa only [biprod.mapIso_hom, biprod.mapIso_inv, Iso.refl_hom,
    Iso.refl_inv, Functor.mapIso_hom] using h'

private abbrev pairObj (X : Pair C) : Pair D :=
  ⟨F.obj X.fst, F.obj X.snd⟩

/-- Map the original common stabilizer and both coordinate isomorphisms using the canonical
biproduct comparison of an additive functor. -/
public def mapRawHom {X Y : Pair C} (f : RawHom X Y) :
    RawHom (⟨F.obj X.fst, F.obj X.snd⟩ : Pair D)
      ⟨F.obj Y.fst, F.obj Y.snd⟩ :=
  letI (A B : C) : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  { stabilizer := F.obj f.stabilizer
    hom₁ := (F.mapBiprod f.stabilizer X.fst).symm.trans (F.mapIso f.hom₁)
    hom₂ := (F.mapBiprod f.stabilizer X.snd).symm.trans (F.mapIso f.hom₂) }

omit [HasZeroObject C] [HasZeroObject D] in
private theorem map_relation_coordinate {s t X Y : C}
    (e : s ≅ t) (f : s ⊞ X ≅ Y) (g : t ⊞ X ≅ Y)
    (h : (stabilizerIso e X).trans g = f) :
    (stabilizerIso (F.mapIso e) (F.obj X)).hom ≫
        ((biprodIso F t X).symm.trans (F.mapIso g)).hom =
      ((biprodIso F s X).symm.trans (F.mapIso f)).hom := by
  have hn := biprodIso_inv_natural F e.hom (𝟙 X)
  simp only [F.map_id] at hn
  have hh := congrArg Iso.hom h
  simp only [stabilizerIso, Iso.trans_hom, biprod.mapIso_hom,
    Iso.refl_hom] at hh
  simp only [stabilizerIso, Iso.trans_hom, Iso.symm_hom,
    biprod.mapIso_hom, Functor.mapIso_hom, Iso.refl_hom]
  calc
    biprod.map (F.map e.hom) (𝟙 (F.obj X)) ≫
          ((biprodIso F t X).inv ≫ F.map g.hom) =
        (biprod.map (F.map e.hom) (𝟙 (F.obj X)) ≫
          (biprodIso F t X).inv) ≫ F.map g.hom :=
      (Category.assoc _ _ _).symm
    _ = ((biprodIso F s X).inv ≫
          F.map (biprod.map e.hom (𝟙 X))) ≫ F.map g.hom := by rw [hn]
    _ = (biprodIso F s X).inv ≫
          F.map (biprod.map e.hom (𝟙 X) ≫ g.hom) := by
      rw [F.map_comp]
      exact Category.assoc _ _ _
    _ = (biprodIso F s X).inv ≫ F.map f.hom := by rw [hh]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mapRawHom_rel {X Y : Pair C} {f g : RawHom X Y}
    (h : f.Rel g) : (mapRawHom F f).Rel (mapRawHom F g) := by
  obtain ⟨e, h₁, h₂⟩ := h
  refine ⟨F.mapIso e, ?_, ?_⟩
  · apply Iso.ext
    exact map_relation_coordinate F e f.hom₁ g.hom₁ h₁
  · apply Iso.ext
    exact map_relation_coordinate F e f.hom₂ g.hom₂ h₂

private theorem mapRawHom_id_rel (X : Pair C) :
    (mapRawHom F (RawHom.id X)).Rel (RawHom.id (pairObj F X)) := by
  refine ⟨F.mapZeroObject, ?_, ?_⟩
  · exact biprodIso_zero_unit F X.fst
  · exact biprodIso_zero_unit F X.snd

omit [HasZeroObject C] [HasZeroObject D] in
private theorem map_composition_coordinate {s t X Y Z : C}
    (f : s ⊞ X ≅ Y) (g : t ⊞ Y ≅ Z) :
    biprod.map (biprodIso F t s).hom (𝟙 (F.obj X)) ≫
        (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
        biprod.map (𝟙 (F.obj t))
          ((biprodIso F s X).inv ≫ F.map f.hom) ≫
        (biprodIso F t Y).inv ≫ F.map g.hom =
      (biprodIso F (t ⊞ s) X).inv ≫ F.map
        ((biprod.associator t s X).hom ≫ biprod.map (𝟙 t) f.hom ≫ g.hom) := by
  have hsplit :
      biprod.map (𝟙 (F.obj t)) ((biprodIso F s X).inv ≫ F.map f.hom) =
        biprod.map (𝟙 (F.obj t)) (biprodIso F s X).inv ≫
          biprod.map (𝟙 (F.obj t)) (F.map f.hom) := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hmove := biprodIso_inv_natural F (𝟙 t) f.hom
  simp only [F.map_id] at hmove
  calc
    biprod.map (biprodIso F t s).hom (𝟙 (F.obj X)) ≫
          (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
          biprod.map (𝟙 (F.obj t))
            ((biprodIso F s X).inv ≫ F.map f.hom) ≫
          (biprodIso F t Y).inv ≫ F.map g.hom =
        (biprod.map (biprodIso F t s).hom (𝟙 (F.obj X)) ≫
          (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
          biprod.map (𝟙 (F.obj t)) (biprodIso F s X).inv) ≫
          (biprod.map (𝟙 (F.obj t)) (F.map f.hom) ≫
            (biprodIso F t Y).inv) ≫ F.map g.hom := by
      rw [hsplit]
      simp only [Category.assoc]
    _ = (biprod.map (biprodIso F t s).hom (𝟙 (F.obj X)) ≫
          (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
          biprod.map (𝟙 (F.obj t)) (biprodIso F s X).inv) ≫
          ((biprodIso F t (s ⊞ X)).inv ≫
            F.map (biprod.map (𝟙 t) f.hom)) ≫ F.map g.hom := by rw [hmove]
    _ = ((biprodIso F (t ⊞ s) X).inv ≫
          F.map (biprod.associator t s X).hom ≫
          (biprodIso F t (s ⊞ X)).hom) ≫
          ((biprodIso F t (s ⊞ X)).inv ≫
            F.map (biprod.map (𝟙 t) f.hom)) ≫ F.map g.hom := by
      rw [biprodIso_associator_inv_hom]
    _ = (biprodIso F (t ⊞ s) X).inv ≫ F.map
          ((biprod.associator t s X).hom ≫
            biprod.map (𝟙 t) f.hom ≫ g.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, F.map_comp]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mapRawHom_comp_rel {X Y Z : Pair C}
    (f : RawHom X Y) (g : RawHom Y Z) :
    (mapRawHom F (f.comp g)).Rel ((mapRawHom F f).comp (mapRawHom F g)) := by
  refine ⟨biprodIso F g.stabilizer f.stabilizer, ?_, ?_⟩
  · apply Iso.ext
    change biprod.map (biprodIso F g.stabilizer f.stabilizer).hom
        (𝟙 (F.obj X.fst)) ≫
        (biprod.associator (F.obj g.stabilizer) (F.obj f.stabilizer)
          (F.obj X.fst)).hom ≫
        biprod.map (𝟙 (F.obj g.stabilizer))
          ((biprodIso F f.stabilizer X.fst).inv ≫ F.map f.hom₁.hom) ≫
        (biprodIso F g.stabilizer Y.fst).inv ≫ F.map g.hom₁.hom =
      (biprodIso F (g.stabilizer ⊞ f.stabilizer) X.fst).inv ≫ F.map
        ((biprod.associator g.stabilizer f.stabilizer X.fst).hom ≫
          biprod.map (𝟙 g.stabilizer) f.hom₁.hom ≫ g.hom₁.hom)
    exact map_composition_coordinate F f.hom₁ g.hom₁
  · apply Iso.ext
    change biprod.map (biprodIso F g.stabilizer f.stabilizer).hom
        (𝟙 (F.obj X.snd)) ≫
        (biprod.associator (F.obj g.stabilizer) (F.obj f.stabilizer)
          (F.obj X.snd)).hom ≫
        biprod.map (𝟙 (F.obj g.stabilizer))
          ((biprodIso F f.stabilizer X.snd).inv ≫ F.map f.hom₂.hom) ≫
        (biprodIso F g.stabilizer Y.snd).inv ≫ F.map g.hom₂.hom =
      (biprodIso F (g.stabilizer ⊞ f.stabilizer) X.snd).inv ≫ F.map
        ((biprod.associator g.stabilizer f.stabilizer X.snd).hom ≫
          biprod.map (𝟙 g.stabilizer) f.hom₂.hom ≫ g.hom₂.hom)
    exact map_composition_coordinate F f.hom₂ g.hom₂

private def mapHom {X Y : Pair C} :
    (X ⟶ Y) → (pairObj F X ⟶ pairObj F Y) :=
  Quotient.map (mapRawHom F) (fun _ _ h => mapRawHom_rel F h)

/-- The functor on the original stabilized Pair category induced by an additive functor. -/
public def pairFunctor : Pair C ⥤ Pair D where
  obj X := ⟨F.obj X.fst, F.obj X.snd⟩
  map {X Y} f := Quotient.map (mapRawHom F) (by
    intro f g h
    exact mapRawHom_rel F h) f
  map_id X := by
    exact _root_.Quotient.sound (mapRawHom_id_rel F X)
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    exact _root_.Quotient.sound (mapRawHom_comp_rel F _ _)

end CategoryTheory.SInverseS

universe uK vK

namespace CategoryTheory.SInverseS

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private def coordinatePairIso {A₁ A₂ B₁ B₂ : D}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) :
    (⟨A₁, A₂⟩ : Pair D) ≅ ⟨B₁, B₂⟩ :=
  (corePairInclusion (C := D)).mapIso
    ((Core.isoMk (x := ⟨A₁⟩) (y := ⟨B₁⟩) e₁).prod
      (Core.isoMk (x := ⟨A₂⟩) (y := ⟨B₂⟩) e₂))

private def coordinatePairRaw {A₁ A₂ B₁ B₂ : D}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) :
    RawHom (⟨A₁, A₂⟩ : Pair D) ⟨B₁, B₂⟩ where
  stabilizer := 0
  hom₁ := (zeroUnitD A₁).trans e₁
  hom₂ := (zeroUnitD A₂).trans e₂

private theorem coordinatePairIso_hom {A₁ A₂ B₁ B₂ : D}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) :
    (coordinatePairIso e₁ e₂).hom = Hom.mk (coordinatePairRaw e₁ e₂) :=
  rfl

private abbrev rightZeroUnit (X : D) : X ⊞ (0 : D) ≅ X :=
  (isoBiprodZero (isZero_zero D)).symm

private theorem left_zero_composition {s X Y Z : D}
    (f : s ⊞ X ≅ Y) (e : Y ≅ Z) :
    (biprod.associator (0 : D) s X).trans
        ((biprod.mapIso (Iso.refl (0 : D)) f).trans ((zeroUnitD Y).trans e)) =
      (biprod.mapIso (zeroUnitD s) (Iso.refl X)).trans (f.trans e) := by
  apply Iso.ext
  change (biprod.associator (0 : D) s X).hom ≫
      biprod.map (𝟙 (0 : D)) f.hom ≫ (zeroUnitD Y).hom ≫ e.hom =
    biprod.map (zeroUnitD s).hom (𝟙 X) ≫ f.hom ≫ e.hom
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ e.hom) (rawComp_id_hom f.hom).symm

private theorem right_zero_cancellation (s X : D) :
    (biprod.mapIso (rightZeroUnit s).symm (Iso.refl X)).trans
        ((biprod.associator s (0 : D) X).trans
          (biprod.mapIso (Iso.refl s) (zeroUnitD X))) = Iso.refl (s ⊞ X) := by
  apply Iso.ext
  change biprod.map (rightZeroUnit s).inv (𝟙 X) ≫
      (biprod.associator s (0 : D) X).hom ≫
      biprod.map (𝟙 s) (zeroUnitD X).hom = 𝟙 (s ⊞ X)
  rw [← rawId_comp_hom]
  apply biprod.hom_ext <;> simp [Category.assoc]

private theorem right_zero_composition {s t X X' Y : D}
    (e : s ≅ t) (k : X ≅ X') (g : t ⊞ X' ≅ Y) :
    (stabilizerIso ((zeroUnitD s).trans (e.trans (rightZeroUnit t).symm)) X).trans
        ((biprod.associator t (0 : D) X).trans
          ((biprod.mapIso (Iso.refl t) ((zeroUnitD X).trans k)).trans g)) =
      (biprod.mapIso (zeroUnitD s) (Iso.refl X)).trans
        ((biprod.mapIso e k).trans g) := by
  apply Iso.ext
  have hsplit :
      biprod.map ((zeroUnitD s).hom ≫ e.hom ≫ (rightZeroUnit t).inv) (𝟙 X) =
        biprod.map (zeroUnitD s).hom (𝟙 X) ≫ biprod.map e.hom (𝟙 X) ≫
          biprod.map (rightZeroUnit t).inv (𝟙 X) := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hunit :
      biprod.map (𝟙 t) ((zeroUnitD X).hom ≫ k.hom) =
        biprod.map (𝟙 t) (zeroUnitD X).hom ≫ biprod.map (𝟙 t) k.hom := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hcancel := congrArg Iso.hom (right_zero_cancellation t X)
  change biprod.map (rightZeroUnit t).inv (𝟙 X) ≫
      (biprod.associator t (0 : D) X).hom ≫
      biprod.map (𝟙 t) (zeroUnitD X).hom = 𝟙 (t ⊞ X) at hcancel
  change biprod.map ((zeroUnitD s).hom ≫ e.hom ≫ (rightZeroUnit t).inv) (𝟙 X) ≫
      (biprod.associator t (0 : D) X).hom ≫
      biprod.map (𝟙 t) ((zeroUnitD X).hom ≫ k.hom) ≫ g.hom =
    biprod.map (zeroUnitD s).hom (𝟙 X) ≫ biprod.map e.hom k.hom ≫ g.hom
  rw [hsplit, hunit]
  have hmiddle :
      biprod.map (rightZeroUnit t).inv (𝟙 X) ≫
          (biprod.associator t (0 : D) X).hom ≫
          (biprod.map (𝟙 t) (zeroUnitD X).hom ≫ biprod.map (𝟙 t) k.hom) =
        biprod.map (𝟙 t) k.hom := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun m => m ≫ biprod.map (𝟙 t) k.hom) hcancel
  have hmiddle' := congrArg (fun m => m ≫ g.hom) hmiddle
  simp only [Category.assoc] at hmiddle' ⊢
  rw [hmiddle']
  have hmap : biprod.map e.hom (𝟙 X) ≫ biprod.map (𝟙 t) k.hom =
      biprod.map e.hom k.hom := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  have hmap' := congrArg (fun m => m ≫ g.hom) hmap
  simp only [Category.assoc] at hmap'
  rw [hmap']

variable (F G : C ⥤ D) [F.Additive] [G.Additive]

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem biprodIso_natIso (α : F ≅ G) (X Y : C) :
    (α.app (X ⊞ Y)).trans (biprodIso G X Y) =
      (biprodIso F X Y).trans (biprod.mapIso (α.app X) (α.app Y)) := by
  apply Iso.ext
  change (α.app (X ⊞ Y)).hom ≫ (biprodIso G X Y).hom =
    (biprodIso F X Y).hom ≫ biprod.map (α.app X).hom (α.app Y).hom
  apply biprod.hom_ext
  · rw [Category.assoc, biprodIso_hom_fst, Category.assoc, biprod.map_fst,
      ← Category.assoc, biprodIso_hom_fst]
    exact (α.hom.naturality biprod.fst).symm
  · rw [Category.assoc, biprodIso_hom_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc, biprodIso_hom_snd]
    exact (α.hom.naturality biprod.snd).symm

omit [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem biprodIso_natIso_inv (α : F ≅ G) (X Y : C) :
    (biprodIso F X Y).symm.trans (α.app (X ⊞ Y)) =
      (biprod.mapIso (α.app X) (α.app Y)).trans (biprodIso G X Y).symm := by
  apply Iso.ext
  have h := congrArg
    (fun k => (biprodIso F X Y).inv ≫ k ≫ (biprodIso G X Y).inv)
    (congrArg Iso.hom (biprodIso_natIso F G α X Y))
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

omit [HasZeroObject C] in
private theorem pair_natIso_coordinate (α : F ≅ G) {s X Y : C}
    (f : s ⊞ X ≅ Y) :
    (stabilizerIso ((zeroUnitD (F.obj s)).trans
        ((α.app s).trans (rightZeroUnit (G.obj s)).symm)) (F.obj X)).trans
        ((biprod.associator (G.obj s) (0 : D) (F.obj X)).trans
          ((biprod.mapIso (Iso.refl (G.obj s))
            ((zeroUnitD (F.obj X)).trans (α.app X))).trans
              ((biprodIso G s X).symm.trans (G.mapIso f)))) =
      (biprod.associator (0 : D) (F.obj s) (F.obj X)).trans
        ((biprod.mapIso (Iso.refl (0 : D))
          ((biprodIso F s X).symm.trans (F.mapIso f))).trans
            ((zeroUnitD (F.obj Y)).trans (α.app Y))) := by
  have hf : (F.mapIso f).trans (α.app Y) =
      (α.app (s ⊞ X)).trans (G.mapIso f) := by
    apply Iso.ext
    exact α.hom.naturality f.hom
  rw [right_zero_composition, left_zero_composition]
  have h := congrArg
    (fun e => (biprod.mapIso (zeroUnitD (F.obj s)) (Iso.refl (F.obj X))).trans
      (e.trans (G.mapIso f))) (biprodIso_natIso_inv F G α s X)
  simpa only [Iso.trans_assoc, ← hf] using h.symm

omit [HasZeroObject C] in
private theorem pair_natIso_raw_rel (α : F ≅ G) {X Y : Pair C}
    (f : RawHom X Y) :
    ((mapRawHom F f).comp
      (coordinatePairRaw (α.app Y.fst) (α.app Y.snd))).Rel
        ((coordinatePairRaw (α.app X.fst) (α.app X.snd)).comp (mapRawHom G f)) := by
  refine ⟨(zeroUnitD (F.obj f.stabilizer)).trans
    ((α.app f.stabilizer).trans (rightZeroUnit (G.obj f.stabilizer)).symm), ?_, ?_⟩
  · exact pair_natIso_coordinate F G α f.hom₁
  · exact pair_natIso_coordinate F G α f.hom₂

/-- A natural isomorphism of additive functors induces the coordinate natural isomorphism
of their stabilized Pair functors. -/
public def pairFunctorNatIso (α : F ≅ G) : pairFunctor F ≅ pairFunctor G :=
  NatIso.ofComponents
    (fun X => (corePairInclusion (C := D)).mapIso
      ((Core.isoMk (x := ⟨F.obj X.fst⟩) (y := ⟨G.obj X.fst⟩) (α.app X.fst)).prod
        (Core.isoMk (x := ⟨F.obj X.snd⟩) (y := ⟨G.obj X.snd⟩) (α.app X.snd))))
    (by
      intro X Y f
      induction f using Quotient.inductionOn with
      | _ f =>
        change Hom.mk ((mapRawHom F f).comp
            (coordinatePairRaw (α.app Y.fst) (α.app Y.snd))) =
          Hom.mk ((coordinatePairRaw (α.app X.fst) (α.app X.snd)).comp
            (mapRawHom G f))
        exact _root_.Quotient.sound (pair_natIso_raw_rel F G α f))

omit [HasZeroObject C] in
private theorem identity_biprodIso (X Y : C) :
    (𝟭 C).mapBiprod X Y = Iso.refl (X ⊞ Y) := by
  apply Iso.ext
  apply biprod.hom_ext
  · exact (biprodIso_hom_fst (𝟭 C) X Y).trans (Category.id_comp biprod.fst).symm
  · exact (biprodIso_hom_snd (𝟭 C) X Y).trans (Category.id_comp biprod.snd).symm

omit [HasZeroObject C] in
private theorem mapRawHom_identity {X Y : Pair C} (f : RawHom X Y) :
    mapRawHom (𝟭 C) f = f := by
  cases f with
  | mk s e₁ e₂ =>
    simp only [mapRawHom, Functor.id_obj, identity_biprodIso,
      Iso.refl_symm, Iso.refl_trans]
    rfl

private theorem mapHom_identity {X Y : Pair C} (f : X ⟶ Y) :
    mapHom (𝟭 C) f = f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    change Hom.mk (mapRawHom (𝟭 C) f) = Hom.mk f
    rw [mapRawHom_identity]

/-- The canonical identity comparison for additive transport of stabilized pairs. -/
public def pairFunctorIdentity : pairFunctor (𝟭 C) ≅ 𝟭 (Pair C) :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    exact (Category.comp_id (mapHom (𝟭 C) f)).trans
      ((mapHom_identity f).trans (Category.id_comp f).symm))

section Composition

variable {K : Type uK} [Category.{vK} K] [Preadditive K]
  [HasZeroObject K] [HasBinaryBiproducts K]
variable (H : D ⥤ K) [H.Additive]

omit [HasZeroObject C] [HasZeroObject D] [HasZeroObject K] [HasBinaryBiproducts K] in
private theorem composite_biprodIso (X Y : C) :
    biprodIso (F ⋙ H) X Y =
      (H.mapIso (biprodIso F X Y)).trans
        (biprodIso H (F.obj X) (F.obj Y)) := by
  apply Iso.ext
  apply biprod.hom_ext
  · have hh := congrArg (fun p => (H.mapIso (biprodIso F X Y)).hom ≫ p)
        (biprodIso_hom_fst H (F.obj X) (F.obj Y))
    have hp :
        ((H.mapIso (biprodIso F X Y)).trans
            (biprodIso H (F.obj X) (F.obj Y))).hom ≫ biprod.fst =
          H.map (F.map biprod.fst) := by
      calc
        _ = H.map (biprodIso F X Y).hom ≫ H.map biprod.fst := by
          simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hh
        _ = H.map ((biprodIso F X Y).hom ≫ biprod.fst) := (H.map_comp _ _).symm
        _ = H.map (F.map biprod.fst) := congrArg H.map (biprodIso_hom_fst F X Y)
    exact (biprodIso_hom_fst (F ⋙ H) X Y).trans hp.symm
  · have hh := congrArg (fun p => (H.mapIso (biprodIso F X Y)).hom ≫ p)
        (biprodIso_hom_snd H (F.obj X) (F.obj Y))
    have hp :
        ((H.mapIso (biprodIso F X Y)).trans
            (biprodIso H (F.obj X) (F.obj Y))).hom ≫ biprod.snd =
          H.map (F.map biprod.snd) := by
      calc
        _ = H.map (biprodIso F X Y).hom ≫ H.map biprod.snd := by
          simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hh
        _ = H.map ((biprodIso F X Y).hom ≫ biprod.snd) := (H.map_comp _ _).symm
        _ = H.map (F.map biprod.snd) := congrArg H.map (biprodIso_hom_snd F X Y)
    exact (biprodIso_hom_snd (F ⋙ H) X Y).trans hp.symm

omit [HasZeroObject C] [HasZeroObject D] [HasZeroObject K] [HasBinaryBiproducts K] in
private theorem composite_coordinate {s X Y : C} (e : s ⊞ X ≅ Y) :
    (biprodIso (F ⋙ H) s X).symm.trans ((F ⋙ H).mapIso e) =
      (biprodIso H (F.obj s) (F.obj X)).symm.trans
        (H.mapIso ((biprodIso F s X).symm.trans (F.mapIso e))) := by
  rw [composite_biprodIso]
  apply Iso.ext
  change ((biprodIso H (F.obj s) (F.obj X)).inv ≫ H.map (biprodIso F s X).inv) ≫
      H.map (F.map e.hom) =
    (biprodIso H (F.obj s) (F.obj X)).inv ≫ H.map
      ((biprodIso F s X).inv ≫ F.map e.hom)
  rw [H.map_comp, Category.assoc]

omit [HasZeroObject C] [HasZeroObject D] [HasZeroObject K] in
private theorem mapRawHom_composite {X Y : Pair C} (f : RawHom X Y) :
    mapRawHom (F ⋙ H) f = mapRawHom H (mapRawHom F f) := by
  cases f with
  | mk s e₁ e₂ =>
    dsimp only [mapRawHom, pairObj, Functor.comp_obj]
    congr 1
    · exact composite_coordinate F H e₁
    · exact composite_coordinate F H e₂

private theorem mapHom_composite {X Y : Pair C} (f : X ⟶ Y) :
    mapHom (F ⋙ H) f = mapHom H (mapHom F f) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    change Hom.mk (mapRawHom (F ⋙ H) f) = Hom.mk (mapRawHom H (mapRawHom F f))
    rw [mapRawHom_composite]

/-- The canonical composition comparison for additive transport of stabilized pairs. -/
public def pairFunctorComposite :
    pairFunctor (F ⋙ H) ≅ pairFunctor F ⋙ pairFunctor H :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id (mapHom (F ⋙ H) f)).trans
      ((mapHom_composite F H f).trans (Category.id_comp (mapHom H (mapHom F f))).symm))

end Composition

variable (E : C ≌ D) [E.functor.Additive]

private def pairUnitCandidate :
    𝟭 (Pair C) ≅ pairFunctor E.functor ⋙ pairFunctor E.inverse :=
  (pairFunctorIdentity (C := C)).symm.trans
    ((pairFunctorNatIso (𝟭 C) (E.functor ⋙ E.inverse) E.unitIso).trans
      (pairFunctorComposite E.functor E.inverse))

private def pairCounitCandidate :
    pairFunctor E.inverse ⋙ pairFunctor E.functor ≅ 𝟭 (Pair D) :=
  (pairFunctorComposite E.inverse E.functor).symm.trans
    ((pairFunctorNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso).trans
      (pairFunctorIdentity (C := D)))

/-- The actual stabilized Pair equivalence induced by an additive equivalence,
with the normalized unit of `Equivalence.mk`. -/
public def pairEquivalence : Pair C ≌ Pair D :=
  Equivalence.mk (pairFunctor E.functor) (pairFunctor E.inverse)
    ((pairFunctorIdentity (C := C)).symm ≪≫
      pairFunctorNatIso (𝟭 C) (E.functor ⋙ E.inverse) E.unitIso ≪≫
        pairFunctorComposite E.functor E.inverse)
    ((pairFunctorComposite E.inverse E.functor).symm ≪≫
      pairFunctorNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso ≪≫
        pairFunctorIdentity (C := D))

private theorem pairEquivalence_unitIso :
    (pairEquivalence E).unitIso =
      Equivalence.adjointifyη (pairUnitCandidate E) (pairCounitCandidate E) :=
  rfl

private theorem pairEquivalence_counitIso :
    (pairEquivalence E).counitIso = pairCounitCandidate E :=
  rfl

end CategoryTheory.SInverseS

namespace CategoryTheory.SInverseS

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mapRawHom_swap {X Y : Pair C} (f : RawHom X Y) :
    mapRawHom F f.swap = (mapRawHom F f).swap := rfl

private theorem pairFunctor_swap :
    swapFunctor (C := C) ⋙ pairFunctor F = pairFunctor F ⋙ swapFunctor (C := D) := by
  apply Functor.hext
  · intro X
    rfl
  · intro X Y f
    induction f using Quotient.inductionOn
    rfl

private theorem core_coordinate {X Y : C} (e : X ≅ Y) :
    (stabilizerIso F.mapZeroObject (F.obj X)).trans
        ((zeroUnitD (F.obj X)).trans (F.mapIso e)) =
      (biprodIso F (0 : C) X).symm.trans
        (F.mapIso ((zeroUnitC X).trans e)) := by
  calc
    _ = ((stabilizerIso F.mapZeroObject (F.obj X)).trans
          (zeroUnitD (F.obj X))).trans (F.mapIso e) := (Iso.trans_assoc _ _ _).symm
    _ = ((biprodIso F (0 : C) X).symm.trans
          (F.mapIso (zeroUnitC X))).trans (F.mapIso e) := by rw [biprodIso_zero_unit]
    _ = _ := by rw [Iso.trans_assoc, ← F.mapIso_trans]

private theorem corePair_raw_rel {X Y : Core C × Core C} (f : X ⟶ Y) :
    (mapRawHom F (RawHom.ofCorePair f)).Rel
      (RawHom.ofCorePair ((F.core.prod F.core).map f)) := by
  refine ⟨F.mapZeroObject, ?_, ?_⟩
  · exact core_coordinate F f.1.iso
  · exact core_coordinate F f.2.iso

private theorem corePair_map {X Y : Core C × Core C} (f : X ⟶ Y) :
    (pairFunctor F).map ((corePairInclusion (C := C)).map f) =
      (corePairInclusion (C := D)).map ((F.core.prod F.core).map f) := by
  change Hom.mk (mapRawHom F (RawHom.ofCorePair f)) =
    Hom.mk (RawHom.ofCorePair ((F.core.prod F.core).map f))
  exact _root_.Quotient.sound (corePair_raw_rel F f)

/-- The original Core-pair inclusion commutes with additive Pair transport. -/
public def corePairIso :
    corePairInclusion (C := C) ⋙ pairFunctor F ≅
      (F.core.prod F.core) ⋙ corePairInclusion (C := D) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id ((pairFunctor F).map (corePairInclusion.map f))).trans
      ((corePair_map F f).trans
        (Category.id_comp (corePairInclusion.map ((F.core.prod F.core).map f))).symm))

private def coreZeroPairIso :
    coreZeroPair (C := C) ⋙ (F.core.prod F.core) ≅
      F.core ⋙ coreZeroPair (C := D) :=
  NatIso.ofComponents
    (fun X => (Core.isoMk (x := ⟨F.obj X.of⟩) (y := ⟨F.obj X.of⟩)
        (Iso.refl (F.obj X.of))).prod
      (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject))
    (by
      intro X Y f
      apply Prod.hom_ext
      · apply Core.hom_ext
        change F.map f.iso.hom ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.iso.hom
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      · apply Core.hom_ext
        change F.map (𝟙 (0 : C)) ≫ F.mapZeroObject.hom = F.mapZeroObject.hom ≫ 𝟙 _
        rw [F.map_id]
        exact (Category.id_comp _).trans (Category.comp_id _).symm)

private theorem positiveCore_natural {X Y : Core C} (f : X ⟶ Y) :
    (pairFunctor F).map ((coreInclusion (C := C)).map f) ≫
        (coordinatePairIso (Iso.refl (F.obj Y.of)) F.mapZeroObject).hom =
      (coordinatePairIso (Iso.refl (F.obj X.of)) F.mapZeroObject).hom ≫
        (coreInclusion (C := D)).map (F.core.map f) := by
  have h := congrArg (fun k => (corePairInclusion (C := D)).map k)
    ((coreZeroPairIso F).hom.naturality f)
  have h' :
      (corePairInclusion (C := D)).map ((F.core.prod F.core).map (coreZeroPair.map f)) ≫
          (coordinatePairIso (Iso.refl (F.obj Y.of)) F.mapZeroObject).hom =
        (coordinatePairIso (Iso.refl (F.obj X.of)) F.mapZeroObject).hom ≫
          corePairInclusion.map (coreZeroPair.map (F.core.map f)) := by
    exact ((corePairInclusion (C := D)).map_comp
      ((F.core.prod F.core).map (coreZeroPair.map f)) ((coreZeroPairIso F).hom.app Y)).symm.trans
        (h.trans ((corePairInclusion (C := D)).map_comp ((coreZeroPairIso F).hom.app X)
          (coreZeroPair.map (F.core.map f))))
  have hm := congrArg
    (fun k => k ≫ (coordinatePairIso (Iso.refl (F.obj Y.of)) F.mapZeroObject).hom)
    (corePair_map F (coreZeroPair.map f))
  exact hm.trans h'

/-- The original positive Core inclusion is compared by the canonical mapped zero object. -/
public def positiveCoreIso :
    coreInclusion (C := C) ⋙ pairFunctor F ≅ F.core ⋙ coreInclusion (C := D) :=
  NatIso.ofComponents
    (fun X => (corePairInclusion (C := D)).mapIso
      ((Core.isoMk (x := ⟨F.obj X.of⟩) (y := ⟨F.obj X.of⟩)
        (Iso.refl (F.obj X.of))).prod
        (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject)))
    (by intro X Y f; exact positiveCore_natural F f)

private def negativeAsSwappedPositive :
    negativeCoreInclusion (C := C) ≅ coreInclusion (C := C) ⋙ swapFunctor :=
  (Functor.rightUnitor negativeCoreInclusion).symm.trans
    ((Functor.isoWhiskerLeft negativeCoreInclusion (swapInvolutionIso (C := C)).symm).trans
      ((Functor.associator negativeCoreInclusion swapFunctor swapFunctor).symm.trans
        (Functor.isoWhiskerRight (negativeCoreSwapIso (C := C)) swapFunctor)))

private theorem coordinatePairIso_swap_hom {A₁ A₂ B₁ B₂ : D}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) :
    (swapFunctor (C := D)).map (coordinatePairIso e₁ e₂).hom =
      (coordinatePairIso e₂ e₁).hom := by
  change Hom.mk (coordinatePairRaw e₁ e₂).swap = Hom.mk (coordinatePairRaw e₂ e₁)
  rfl

private theorem pairFunctor_swap_map {X Y : Pair C} (f : X ⟶ Y) :
    (swapFunctor (C := D)).map ((pairFunctor F).map f) =
      (pairFunctor F).map ((swapFunctor (C := C)).map f) := by
  induction f using Quotient.inductionOn
  rfl

private theorem negativeCore_natural {X Y : Core C} (f : X ⟶ Y) :
    (pairFunctor F).map ((negativeCoreInclusion (C := C)).map f) ≫
        (coordinatePairIso F.mapZeroObject (Iso.refl (F.obj Y.of))).hom =
      (coordinatePairIso F.mapZeroObject (Iso.refl (F.obj X.of))).hom ≫
        (negativeCoreInclusion (C := D)).map (F.core.map f) := by
  apply (swapEquivalence (C := D)).fullyFaithfulFunctor.map_injective
  have hc : (swapFunctor (C := C)).map (negativeCoreInclusion.map f) =
      coreInclusion.map f := rfl
  have hd : (swapFunctor (C := D)).map (negativeCoreInclusion.map (F.core.map f)) =
      coreInclusion.map (F.core.map f) := rfl
  change (swapFunctor (C := D)).map
      ((pairFunctor F).map (negativeCoreInclusion.map f) ≫
        (coordinatePairIso F.mapZeroObject (Iso.refl (F.obj Y.of))).hom) =
    (swapFunctor (C := D)).map
      ((coordinatePairIso F.mapZeroObject (Iso.refl (F.obj X.of))).hom ≫
        negativeCoreInclusion.map (F.core.map f))
  have ha := (pairFunctor_swap_map F (negativeCoreInclusion.map f)).trans
    (congrArg (pairFunctor F).map hc)
  have hy := coordinatePairIso_swap_hom F.mapZeroObject (Iso.refl (F.obj Y.of))
  have hx := coordinatePairIso_swap_hom F.mapZeroObject (Iso.refl (F.obj X.of))
  have hl := (swapFunctor (C := D)).map_comp
    ((pairFunctor F).map (negativeCoreInclusion.map f))
    (coordinatePairIso F.mapZeroObject (Iso.refl (F.obj Y.of))).hom
  have h₁ := congrArg₂ (fun m n => m ≫ n) ha hy
  have h₂ := (congrArg₂ (fun m n => m ≫ n) hx hd).symm
  have hr := ((swapFunctor (C := D)).map_comp
    (coordinatePairIso F.mapZeroObject (Iso.refl (F.obj X.of))).hom
    (negativeCoreInclusion.map (F.core.map f))).symm
  exact hl.trans (h₁.trans ((positiveCore_natural F f).trans (h₂.trans hr)))

/-- The genuine strict-zero-fiber negative Core inclusion is compared by the canonical
mapped zero object. -/
public def negativeCoreIso :
    negativeCoreInclusion (C := C) ⋙ pairFunctor F ≅
      F.core ⋙ negativeCoreInclusion (C := D) :=
  NatIso.ofComponents
    (fun X => (corePairInclusion (C := D)).mapIso
      ((Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
        (Core.isoMk (x := ⟨F.obj X.of⟩) (y := ⟨F.obj X.of⟩)
          (Iso.refl (F.obj X.of)))))
    (by intro X Y f; exact negativeCore_natural F f)

omit [HasZeroObject C] in
private theorem swapStabilizer_fst (A s X : C) :
    (swapStabilizerIso A s X).hom ≫ biprod.fst =
      (biprod.snd : s ⊞ (A ⊞ X) ⟶ A ⊞ X) ≫ biprod.fst := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [HasZeroObject C] in
private theorem swapStabilizer_snd_fst (A s X : C) :
    (swapStabilizerIso A s X).hom ≫ biprod.snd ≫ biprod.fst =
      (biprod.fst : s ⊞ (A ⊞ X) ⟶ s) := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [HasZeroObject C] in
private theorem swapStabilizer_snd_snd (A s X : C) :
    (swapStabilizerIso A s X).hom ≫ biprod.snd ≫ biprod.snd =
      (biprod.snd : s ⊞ (A ⊞ X) ⟶ A ⊞ X) ≫ biprod.snd := by
  apply biprod.hom_ext'
  · simp
  · apply biprod.hom_ext' <;> simp

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mappedSwapStabilizerIso (A s X : C) :
    (F.mapIso (swapStabilizerIso A s X)).trans
        ((biprodIso F A (s ⊞ X)).trans
          (biprod.mapIso (Iso.refl (F.obj A)) (biprodIso F s X))) =
      (biprodIso F s (A ⊞ X)).trans
        ((biprod.mapIso (Iso.refl (F.obj s)) (biprodIso F A X)).trans
          (swapStabilizerIso (F.obj A) (F.obj s) (F.obj X))) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, biprod.mapIso_hom, Iso.refl_hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      biprodIso_hom_fst, ← F.map_comp, swapStabilizer_fst]
    rw [biprod.map_snd_assoc, biprodIso_hom_fst, biprodIso_hom_snd_assoc, F.map_comp]
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_snd,
        biprodIso_hom_fst, swapStabilizer_snd_fst]
      rw [biprodIso_hom_snd_assoc, biprod.map_fst, Category.comp_id, biprodIso_hom_fst]
      simp only [← F.map_comp, swapStabilizer_snd_fst]
    · simp only [Category.assoc, biprod.map_snd,
        biprodIso_hom_snd, swapStabilizer_snd_snd]
      rw [biprodIso_hom_snd_assoc, biprod.map_snd_assoc,
        biprodIso_hom_snd, biprodIso_hom_snd_assoc]
      simp only [← F.map_comp, swapStabilizer_snd_snd]

private theorem positiveCoreIso_app (X : Core C) :
    (positiveCoreIso F).app X =
      coordinatePairIso (Iso.refl (F.obj X.of)) F.mapZeroObject := by
  rfl

private theorem negativeCoreIso_app (X : Core C) :
    (negativeCoreIso F).app X =
      coordinatePairIso F.mapZeroObject (Iso.refl (F.obj X.of)) := by
  rfl

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mappedSwapStabilizer_inv_hom (A s X : C) :
    biprod.map (𝟙 (F.obj s)) (biprodIso F A X).hom ≫
        (swapStabilizerIso (F.obj A) (F.obj s) (F.obj X)).hom ≫
        biprod.map (𝟙 (F.obj A)) (biprodIso F s X).inv =
      (biprodIso F s (A ⊞ X)).inv ≫ F.map (swapStabilizerIso A s X).hom ≫
        (biprodIso F A (s ⊞ X)).hom := by
  have h := congrArg
    (fun k => (biprodIso F s (A ⊞ X)).inv ≫ k ≫
      (biprod.mapIso (Iso.refl (F.obj A)) (biprodIso F s X)).inv)
    (congrArg Iso.hom (mappedSwapStabilizerIso F A s X))
  have h' :
      (biprod.mapIso (Iso.refl (F.obj s)) (biprodIso F A X)).hom ≫
          (swapStabilizerIso (F.obj A) (F.obj s) (F.obj X)).hom ≫
          (biprod.mapIso (Iso.refl (F.obj A)) (biprodIso F s X)).inv =
        (biprodIso F s (A ⊞ X)).inv ≫ (F.mapIso (swapStabilizerIso A s X)).hom ≫
          (biprodIso F A (s ⊞ X)).hom := by
    simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using h.symm
  simpa only [biprod.mapIso_hom, biprod.mapIso_inv, Iso.refl_hom,
    Iso.refl_inv, Functor.mapIso_hom] using h'

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mapped_translation_coordinate (A : C) {s X Y : C}
    (f : s ⊞ X ≅ Y) :
    ((biprodIso F s (A ⊞ X)).symm.trans
        (F.mapIso ((swapStabilizerIso A s X).trans
          (biprod.mapIso (Iso.refl A) f)))).trans (biprodIso F A Y) =
      (biprod.mapIso (Iso.refl (F.obj s)) (biprodIso F A X)).trans
        ((swapStabilizerIso (F.obj A) (F.obj s) (F.obj X)).trans
          (biprod.mapIso (Iso.refl (F.obj A))
            ((biprodIso F s X).symm.trans (F.mapIso f)))) := by
  apply Iso.ext
  have hn := biprodIso_natural F (𝟙 A) f.hom
  simp only [F.map_id] at hn
  have hs := mappedSwapStabilizer_inv_hom F A s X
  have hb :
      biprod.map (𝟙 (F.obj A)) (biprodIso F s X).inv ≫
          biprod.map (𝟙 (F.obj A)) (F.map f.hom) =
        biprod.map (𝟙 (F.obj A)) ((biprodIso F s X).inv ≫ F.map f.hom) := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  change ((biprodIso F s (A ⊞ X)).inv ≫ F.map
      ((swapStabilizerIso A s X).hom ≫ biprod.map (𝟙 A) f.hom)) ≫
        (biprodIso F A Y).hom =
    biprod.map (𝟙 (F.obj s)) (biprodIso F A X).hom ≫
      (swapStabilizerIso (F.obj A) (F.obj s) (F.obj X)).hom ≫
      biprod.map (𝟙 (F.obj A)) ((biprodIso F s X).inv ≫ F.map f.hom)
  rw [F.map_comp]
  have hn' := congrArg
    (fun k => (biprodIso F s (A ⊞ X)).inv ≫
      F.map (swapStabilizerIso A s X).hom ≫ k) hn
  have hs' := congrArg (fun k => k ≫ biprod.map (𝟙 (F.obj A)) (F.map f.hom)) hs
  simp only [Category.assoc] at hn' hs' ⊢
  rw [hn', ← hs']
  rw [hb]

omit [HasZeroObject D] in
private theorem biprod_mapIso_refl (A B : D) :
    biprod.mapIso (Iso.refl A) (Iso.refl B) = Iso.refl (A ⊞ B) := by
  apply Iso.ext
  apply biprod.hom_ext <;> simp

private theorem unchanged_translation_coordinate {s X Y : D} (f : s ⊞ X ≅ Y) :
    (stabilizerIso ((zeroUnitD s).trans (rightZeroUnit s).symm) X).trans
        ((biprod.associator s (0 : D) X).trans
          ((biprod.mapIso (Iso.refl s) ((zeroUnitD X).trans (Iso.refl X))).trans f)) =
      (biprod.associator (0 : D) s X).trans
        ((biprod.mapIso (Iso.refl (0 : D)) f).trans
          ((zeroUnitD Y).trans (Iso.refl Y))) := by
  have hr := right_zero_composition (Iso.refl s) (Iso.refl X) f
  have hl := left_zero_composition f (Iso.refl Y)
  simp only [Iso.refl_trans, Iso.trans_refl, biprod_mapIso_refl] at hr hl
  simpa only [Iso.refl_trans, Iso.trans_refl] using hr.trans hl.symm

omit [HasZeroObject C] in
private theorem translation_naturality_coordinate (A : C) {s X Y : C}
    (f : s ⊞ X ≅ Y) :
    (stabilizerIso ((zeroUnitD (F.obj s)).trans
        (rightZeroUnit (F.obj s)).symm) (F.obj (A ⊞ X))).trans
        ((biprod.associator (F.obj s) (0 : D) (F.obj (A ⊞ X))).trans
          ((biprod.mapIso (Iso.refl (F.obj s))
            ((zeroUnitD (F.obj (A ⊞ X))).trans (biprodIso F A X))).trans
              ((swapStabilizerIso (F.obj A) (F.obj s) (F.obj X)).trans
                (biprod.mapIso (Iso.refl (F.obj A))
                  ((biprodIso F s X).symm.trans (F.mapIso f)))))) =
      (biprod.associator (0 : D) (F.obj s) (F.obj (A ⊞ X))).trans
        ((biprod.mapIso (Iso.refl (0 : D))
          ((biprodIso F s (A ⊞ X)).symm.trans
            (F.mapIso ((swapStabilizerIso A s X).trans
              (biprod.mapIso (Iso.refl A) f))))).trans
          ((zeroUnitD (F.obj (A ⊞ Y))).trans (biprodIso F A Y))) := by
  have hr := right_zero_composition (Iso.refl (F.obj s)) (biprodIso F A X)
    ((swapStabilizerIso (F.obj A) (F.obj s) (F.obj X)).trans
      (biprod.mapIso (Iso.refl (F.obj A))
        ((biprodIso F s X).symm.trans (F.mapIso f))))
  have hl := left_zero_composition
    ((biprodIso F s (A ⊞ X)).symm.trans
      (F.mapIso ((swapStabilizerIso A s X).trans (biprod.mapIso (Iso.refl A) f))))
    (biprodIso F A Y)
  have hc := mapped_translation_coordinate F A f
  have hc' := congrArg
    (fun k => (biprod.mapIso (zeroUnitD (F.obj s))
      (Iso.refl (F.obj (A ⊞ X)))).trans k) hc
  simpa only [Iso.refl_trans] using (hr.trans hc'.symm).trans hl.symm

omit [HasZeroObject C] in
private theorem translateFirst_raw_rel (A : C) {X Y : Pair C} (f : RawHom X Y) :
    ((mapRawHom F (f.translateFirst A)).comp
      (coordinatePairRaw (biprodIso F A Y.fst) (Iso.refl (F.obj Y.snd)))).Rel
        ((coordinatePairRaw (biprodIso F A X.fst) (Iso.refl (F.obj X.snd))).comp
          ((mapRawHom F f).translateFirst (F.obj A))) := by
  refine ⟨(zeroUnitD (F.obj f.stabilizer)).trans
    (rightZeroUnit (F.obj f.stabilizer)).symm, ?_, ?_⟩
  · exact translation_naturality_coordinate F A f.hom₁
  · exact unchanged_translation_coordinate
      ((biprodIso F f.stabilizer X.snd).symm.trans (F.mapIso f.hom₂))

omit [HasZeroObject C] in
private theorem translateSecond_raw_rel (A : C) {X Y : Pair C} (f : RawHom X Y) :
    ((mapRawHom F (f.translateSecond A)).comp
      (coordinatePairRaw (Iso.refl (F.obj Y.fst)) (biprodIso F A Y.snd))).Rel
        ((coordinatePairRaw (Iso.refl (F.obj X.fst)) (biprodIso F A X.snd)).comp
          ((mapRawHom F f).translateSecond (F.obj A))) := by
  refine ⟨(zeroUnitD (F.obj f.stabilizer)).trans
    (rightZeroUnit (F.obj f.stabilizer)).symm, ?_, ?_⟩
  · exact unchanged_translation_coordinate
      ((biprodIso F f.stabilizer X.fst).symm.trans (F.mapIso f.hom₁))
  · exact translation_naturality_coordinate F A f.hom₂

/-- The original first-coordinate translation commutes with additive Pair transport
through the canonical biproduct comparison. -/
public def translateFirstIso (A : C) :
    translateFirstFunctor A ⋙ pairFunctor F ≅
      pairFunctor F ⋙ translateFirstFunctor (F.obj A) :=
  letI (B Z : C) : PreservesBinaryBiproduct B Z F :=
    preservesBinaryBiproduct_of_preservesBiproduct F B Z
  NatIso.ofComponents
    (fun X => (corePairInclusion (C := D)).mapIso
      ((Core.isoMk (x := ⟨F.obj (A ⊞ X.fst)⟩)
        (y := ⟨F.obj A ⊞ F.obj X.fst⟩) (F.mapBiprod A X.fst)).prod
        (Core.isoMk (x := ⟨F.obj X.snd⟩) (y := ⟨F.obj X.snd⟩)
          (Iso.refl (F.obj X.snd)))))
    (by
      intro X Y f
      induction f using Quotient.inductionOn with
      | _ f =>
        exact (show Hom.mk ((mapRawHom F (f.translateFirst A)).comp
              (coordinatePairRaw (biprodIso F A Y.fst) (Iso.refl (F.obj Y.snd)))) =
            Hom.mk ((coordinatePairRaw (biprodIso F A X.fst) (Iso.refl (F.obj X.snd))).comp
              ((mapRawHom F f).translateFirst (F.obj A))) from
          _root_.Quotient.sound (translateFirst_raw_rel F A f)))

/-- The original second-coordinate translation commutes with additive Pair transport
through the canonical biproduct comparison. -/
public def translateSecondIso (A : C) :
    translateSecondFunctor A ⋙ pairFunctor F ≅
      pairFunctor F ⋙ translateSecondFunctor (F.obj A) :=
  letI (B Z : C) : PreservesBinaryBiproduct B Z F :=
    preservesBinaryBiproduct_of_preservesBiproduct F B Z
  NatIso.ofComponents
    (fun X => (corePairInclusion (C := D)).mapIso
      ((Core.isoMk (x := ⟨F.obj X.fst⟩) (y := ⟨F.obj X.fst⟩)
        (Iso.refl (F.obj X.fst))).prod
        (Core.isoMk (x := ⟨F.obj (A ⊞ X.snd)⟩)
          (y := ⟨F.obj A ⊞ F.obj X.snd⟩) (F.mapBiprod A X.snd))))
    (by
      intro X Y f
      induction f using Quotient.inductionOn with
      | _ f =>
        exact (show Hom.mk ((mapRawHom F (f.translateSecond A)).comp
              (coordinatePairRaw (Iso.refl (F.obj Y.fst)) (biprodIso F A Y.snd))) =
            Hom.mk ((coordinatePairRaw (Iso.refl (F.obj X.fst)) (biprodIso F A X.snd)).comp
              ((mapRawHom F f).translateSecond (F.obj A))) from
          _root_.Quotient.sound (translateSecond_raw_rel F A f)))

variable (E : C ≌ D) [E.functor.Additive]

private theorem actualPair_obj (X : Pair C) :
    (pairEquivalence E).functor.obj X = ⟨E.functor.obj X.fst, E.functor.obj X.snd⟩ := rfl

private theorem actualPair_map {X Y : Pair C} (f : RawHom X Y) :
    (pairEquivalence E).functor.map (Hom.mk f) = Hom.mk (mapRawHom E.functor f) := rfl

private def actualPositiveCoreIso :
    coreInclusion (C := C) ⋙ (pairEquivalence E).functor ≅
      E.core.functor ⋙ coreInclusion (C := D) := positiveCoreIso E.functor

private def actualNegativeCoreIso :
    negativeCoreInclusion (C := C) ⋙ (pairEquivalence E).functor ≅
      E.core.functor ⋙ negativeCoreInclusion (C := D) := negativeCoreIso E.functor

private def actualCorePairIso :
    corePairInclusion (C := C) ⋙ (pairEquivalence E).functor ≅
      (E.core.functor.prod E.core.functor) ⋙ corePairInclusion (C := D) :=
  corePairIso E.functor

private theorem actualSwap :
    swapFunctor (C := C) ⋙ (pairEquivalence E).functor =
      (pairEquivalence E).functor ⋙ swapFunctor (C := D) := pairFunctor_swap E.functor

private theorem actualPositiveCoreIso_app (X : Core C) :
    (actualPositiveCoreIso E).app X =
      coordinatePairIso (Iso.refl (E.functor.obj X.of)) E.functor.mapZeroObject := rfl

private theorem actualNegativeCoreIso_app (X : Core C) :
    (actualNegativeCoreIso E).app X =
      coordinatePairIso E.functor.mapZeroObject (Iso.refl (E.functor.obj X.of)) := rfl

private def actualTranslateFirstIso (A : C) :
    translateFirstFunctor A ⋙ (pairEquivalence E).functor ≅
      (pairEquivalence E).functor ⋙ translateFirstFunctor (E.functor.obj A) :=
  translateFirstIso E.functor A

private def actualTranslateSecondIso (A : C) :
    translateSecondFunctor A ⋙ (pairEquivalence E).functor ≅
      (pairEquivalence E).functor ⋙ translateSecondFunctor (E.functor.obj A) :=
  translateSecondIso E.functor A

private theorem actualTranslateFirstIso_app (A : C) (X : Pair C) :
    (actualTranslateFirstIso E A).app X =
      coordinatePairIso (biprodIso E.functor A X.fst) (Iso.refl (E.functor.obj X.snd)) := rfl

private theorem actualTranslateSecondIso_app (A : C) (X : Pair C) :
    (actualTranslateSecondIso E A).app X =
      coordinatePairIso (Iso.refl (E.functor.obj X.fst)) (biprodIso E.functor A X.snd) := rfl

end CategoryTheory.SInverseS

namespace CategoryTheory.SInverseS

open Algebra

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

section ForwardTransport

variable (F : C ⥤ D) [F.Additive]

/-- The original distinguished pair is compared by the two canonical zero isomorphisms. -/
public def zeroPairIso :
    (pairFunctor F).obj (⟨0, 0⟩ : Pair C) ≅ (⟨0, 0⟩ : Pair D) :=
  (corePairInclusion (C := D)).mapIso
    ((Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
      (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject))

private theorem zeroPairIso_hom :
    (zeroPairIso F).hom =
      Hom.mk (coordinatePairRaw F.mapZeroObject F.mapZeroObject) := rfl

omit [HasBinaryBiproducts C] in
private theorem zeroPairIso_raw_stabilizer :
    (coordinatePairRaw F.mapZeroObject F.mapZeroObject).stabilizer =
      (0 : D) := rfl

/-- Transport the original second-then-first translate-to-zero functor. -/
public def toZeroIso (X : Pair C) :
    translateToZeroFunctor X ⋙ (pairFunctor F) ≅
      (pairFunctor F) ⋙
        translateToZeroFunctor ((pairFunctor F).obj X) :=
  Functor.associator (translateSecondFunctor X.fst)
      (translateFirstFunctor X.snd) (pairFunctor F) ≪≫
    Functor.isoWhiskerLeft (translateSecondFunctor X.fst)
      (translateFirstIso F X.snd) ≪≫
    (Functor.associator (translateSecondFunctor X.fst)
      (pairFunctor F)
      (translateFirstFunctor (F.obj X.snd))).symm ≪≫
    Functor.isoWhiskerRight (translateSecondIso F X.fst)
      (translateFirstFunctor (F.obj X.snd)) ≪≫
    Functor.associator (pairFunctor F)
      (translateSecondFunctor (F.obj X.fst))
      (translateFirstFunctor (F.obj X.snd))

/-- The component keeps the original whiskered second factor. -/
private theorem toZeroIso_app (X Y : Pair C) :
    (toZeroIso F X).app Y =
      (translateFirstIso F X.snd).app
          ((translateSecondFunctor X.fst).obj Y) ≪≫
        (translateFirstFunctor (F.obj X.snd)).mapIso
          ((translateSecondIso F X.fst).app Y) := by
  apply Iso.ext
  change
    (𝟙 _ ≫
      (translateFirstIso F X.snd).hom.app
        ((translateSecondFunctor X.fst).obj Y) ≫
      𝟙 _ ≫
      (translateFirstFunctor (F.obj X.snd)).map
        ((translateSecondIso F X.fst).hom.app Y) ≫ 𝟙 _) = _
  simp only [Category.comp_id, Category.id_comp]
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_hom]

/-- Both coordinate factors are fixed; the second remains the actual first translation map. -/
private theorem toZeroIso_app_coordinates (X Y : Pair C) :
    (toZeroIso F X).app Y =
      coordinatePairIso (biprodIso F X.snd Y.fst)
          (Iso.refl (F.obj (X.fst ⊞ Y.snd))) ≪≫
        (translateFirstFunctor (F.obj X.snd)).mapIso
          (coordinatePairIso (Iso.refl (F.obj Y.fst))
            (biprodIso F X.fst Y.snd)) := by
  rw [toZeroIso_app]
  rfl

omit [HasZeroObject C] in
private theorem diagonal_coordinate (F : C ⥤ D) [F.Additive] (A X : C) :
    (stabilizerIso (zeroUnitD (F.obj A)) (F.obj X)).trans
        (Iso.refl (F.obj A ⊞ F.obj X)) =
      (biprod.associator (0 : D) (F.obj A) (F.obj X)).trans
        ((biprod.mapIso (Iso.refl (0 : D))
          ((biprodIso F A X).symm.trans (F.mapIso (Iso.refl (A ⊞ X))))).trans
          ((zeroUnitD (F.obj (A ⊞ X))).trans (biprodIso F A X))) := by
  have hcancel :
      ((biprodIso F A X).symm.trans (F.mapIso (Iso.refl (A ⊞ X)))).trans
          (biprodIso F A X) = Iso.refl (F.obj A ⊞ F.obj X) := by
    apply Iso.ext
    change ((biprodIso F A X).inv ≫ F.map (𝟙 (A ⊞ X))) ≫
      (biprodIso F A X).hom = 𝟙 _
    rw [F.map_id, Category.comp_id]
    exact (biprodIso F A X).inv_hom_id
  have h := left_zero_composition
    ((biprodIso F A X).symm.trans (F.mapIso (Iso.refl (A ⊞ X))))
    (biprodIso F A X)
  rw [hcancel] at h
  exact h.symm

omit [HasZeroObject C] in
/-- The stabilizer change is the canonical left-zero unit, not an inverse diagonal arrow. -/
private theorem diagonal_raw_rel (F : C ⥤ D) [F.Additive] (A : C) (X : Pair C) :
    ((mapRawHom F (RawHom.diagonalAdd A X)).comp
      (coordinatePairRaw (biprodIso F A X.fst) (biprodIso F A X.snd))).Rel
        (RawHom.diagonalAdd (F.obj A) (pairObj F X)) := by
  refine ⟨zeroUnitD (F.obj A), ?_, ?_⟩
  · exact diagonal_coordinate F A X.fst
  · exact diagonal_coordinate F A X.snd

/-- The independently constructed diagonal arrow is retained by the actual Pair map. -/
private theorem diagonal_map (A : C) (X : Pair C) :
    (pairFunctor F).map (diagonalAddHom A X) ≫
        (coordinatePairIso (biprodIso F A X.fst)
          (biprodIso F A X.snd)).hom =
      diagonalAddHom (F.obj A) ((pairFunctor F).obj X) := by
  exact (show Hom.mk
      ((mapRawHom F (RawHom.diagonalAdd A X)).comp
        (coordinatePairRaw (biprodIso F A X.fst)
          (biprodIso F A X.snd))) =
      Hom.mk (RawHom.diagonalAdd (F.obj A)
        (pairObj F X)) from
    _root_.Quotient.sound (diagonal_raw_rel F A X))

/-- This is the existing cross-universe Grothendieck map of the actual additive functor. -/
private def grothMap (F : C ⥤ D) [F.Additive] :
    GrothendieckAddGroup (Skeleton C) →+ GrothendieckAddGroup (Skeleton D) :=
  GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F))

private theorem grothMap_of (F : C ⥤ D) [F.Additive] (X : C) :
    grothMap F (GrothendieckAddGroup.of (toSkeleton X)) =
      GrothendieckAddGroup.of (toSkeleton (F.obj X)) := by
  rw [grothMap, GrothendieckAddGroup.map_of, Skeleton.mapAddMonoidHom_toSkeleton]

/-- The map preserves the difference of every pair, including mixed components. -/
private theorem difference_map (X : Pair C) :
    grothMap F X.difference =
      ((pairFunctor F).obj X).difference := by
  change grothMap F
      (GrothendieckAddGroup.of (toSkeleton X.fst) -
        GrothendieckAddGroup.of (toSkeleton X.snd)) =
    GrothendieckAddGroup.of (toSkeleton (F.obj X.fst)) -
      GrothendieckAddGroup.of (toSkeleton (F.obj X.snd))
  rw [map_sub, grothMap_of, grothMap_of]

/-- The raw group value is wrapped as an actual discrete-category object. -/
private def differenceMapFunctor (F : C ⥤ D) [F.Additive] :
    Discrete (GrothendieckAddGroup (Skeleton C)) ⥤
      Discrete (GrothendieckAddGroup (Skeleton D)) :=
  Discrete.functor (fun k => Discrete.mk (grothMap F k))

/-- The comparison uses the inverse orientation of the proved difference equality. -/
public def differenceIso :
    (pairFunctor F) ⋙ differenceFunctor (C := D) ≅
      differenceFunctor (C := C) ⋙
        Discrete.functor (fun k : GrothendieckAddGroup (Skeleton C) =>
          Discrete.mk (GrothendieckAddGroup.map
            (Skeleton.mapAddMonoidHom (F := F)) k)) :=
  NatIso.ofComponents
    (fun X => eqToIso (by
      exact congrArg
        (fun k : GrothendieckAddGroup (Skeleton D) => Discrete.mk k)
        (difference_map F X).symm))
    (by intro X Y f; exact Subsingleton.elim _ _)

/-- The square is for the original map on every categorical connected component. -/
private theorem components_map (a : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((pairFunctor F).mapConnectedComponents a) =
      grothMap F (connectedComponentsToGrothendieck a) := by
  induction a using Quotient.inductionOn with
  | _ X =>
    simpa only [Functor.mapConnectedComponents_mk,
      connectedComponentsToGrothendieck_mk] using (difference_map F X).symm

private theorem components_positive (X : Core C) :
    connectedComponentsToGrothendieck
        ((pairFunctor F).mapConnectedComponents
          (ConnectedComponents.mk ((coreInclusion (C := C)).obj X))) =
      GrothendieckAddGroup.of (toSkeleton (F.obj X.of)) := by
  rw [components_map, connectedComponentsToGrothendieck_mk]
  have h : ((coreInclusion (C := C)).obj X).difference =
      GrothendieckAddGroup.of (toSkeleton X.of) :=
    difference_coreInclusion_obj_as X
  rw [h, grothMap_of]

/-- The negative source is the original strict-zero-fiber inclusion. -/
private theorem components_negative (X : Core C) :
    connectedComponentsToGrothendieck
        ((pairFunctor F).mapConnectedComponents
          (ConnectedComponents.mk ((negativeCoreInclusion (C := C)).obj X))) =
      -GrothendieckAddGroup.of (toSkeleton (F.obj X.of)) := by
  rw [components_map, connectedComponentsToGrothendieck_mk]
  have h : ((negativeCoreInclusion (C := C)).obj X).difference =
      -GrothendieckAddGroup.of (toSkeleton X.of) := by
    change GrothendieckAddGroup.of (toSkeleton (0 : C)) -
      GrothendieckAddGroup.of (toSkeleton X.of) = _
    rw [Skeleton.toSkeleton_zero, map_zero, zero_sub]
  rw [h, map_neg, grothMap_of]

private theorem components_swap (a : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((swapFunctor (C := D)).mapConnectedComponents
          ((pairFunctor F).mapConnectedComponents a)) =
      -grothMap F (connectedComponentsToGrothendieck a) := by
  rw [connectedComponentsToGrothendieck_mapConnectedComponents_swap, components_map]

private theorem components_first (A : C) (a : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((translateFirstFunctor (F.obj A)).mapConnectedComponents
          ((pairFunctor F).mapConnectedComponents a)) =
      GrothendieckAddGroup.of (toSkeleton (F.obj A)) +
        grothMap F (connectedComponentsToGrothendieck a) := by
  rw [connectedComponentsToGrothendieck_mapConnectedComponents_translateFirst,
    components_map]

private theorem components_second (A : C) (a : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((translateSecondFunctor (F.obj A)).mapConnectedComponents
          ((pairFunctor F).mapConnectedComponents a)) =
      grothMap F (connectedComponentsToGrothendieck a) -
        GrothendieckAddGroup.of (toSkeleton (F.obj A)) := by
  rw [connectedComponentsToGrothendieck_mapConnectedComponents_translateSecond,
    components_map]

/-- The formula retains every source component before specializing the selected one. -/
private theorem components_toZero (X : Pair C) (a : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((translateToZeroFunctor ((pairFunctor F).obj X)).mapConnectedComponents
          ((pairFunctor F).mapConnectedComponents a)) =
      grothMap F (connectedComponentsToGrothendieck a - X.difference) := by
  rw [connectedComponentsToGrothendieck_mapConnectedComponents_translateToZero,
    components_map, ← difference_map]
  exact (map_sub (grothMap F) _ _).symm

private theorem components_toZero_commutes (X : Pair C)
    (a : ConnectedComponents (Pair C)) :
    (translateToZeroFunctor ((pairFunctor F).obj X)).mapConnectedComponents
        ((pairFunctor F).mapConnectedComponents a) =
      (pairFunctor F).mapConnectedComponents
        ((translateToZeroFunctor X).mapConnectedComponents a) := by
  apply connectedComponentsToGrothendieck_injective (C := D)
  rw [components_toZero, components_map,
    connectedComponentsToGrothendieck_mapConnectedComponents_translateToZero]

private theorem components_toZero_selected (X : Pair C) :
    connectedComponentsToGrothendieck
        ((translateToZeroFunctor ((pairFunctor F).obj X)).mapConnectedComponents
          ((pairFunctor F).mapConnectedComponents (ConnectedComponents.mk X))) =
      0 := by
  rw [components_toZero, connectedComponentsToGrothendieck_mk, sub_self, map_zero]

end ForwardTransport

section GrothEquivalence

variable (E : C ≌ D) [E.functor.Additive]

/-- The skeleton inverse is derived from the original E unit, in its original direction. -/
private theorem skeleton_inverse_left :
    (Skeleton.mapAddMonoidHom (F := E.inverse)).comp
        (Skeleton.mapAddMonoidHom (F := E.functor)) =
      AddMonoidHom.id (Skeleton C) := by
  rw [← Skeleton.mapAddMonoidHom_comp]
  exact (Skeleton.mapAddMonoidHom_eq_of_iso E.unitIso).symm.trans
    (Skeleton.mapAddMonoidHom_id (C := C))

/-- The other skeleton inverse is derived from the original E counit. -/
private theorem skeleton_inverse_right :
    (Skeleton.mapAddMonoidHom (F := E.functor)).comp
        (Skeleton.mapAddMonoidHom (F := E.inverse)) =
      AddMonoidHom.id (Skeleton D) := by
  rw [← Skeleton.mapAddMonoidHom_comp]
  exact (Skeleton.mapAddMonoidHom_eq_of_iso E.counitIso).trans
    (Skeleton.mapAddMonoidHom_id (C := D))

private theorem groth_inverse_left :
    (grothMap E.inverse).comp (grothMap E.functor) =
      AddMonoidHom.id (GrothendieckAddGroup (Skeleton C)) := by
  change (GrothendieckAddGroup.map
      (Skeleton.mapAddMonoidHom (F := E.inverse))).comp
      (GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.functor))) = _
  rw [← GrothendieckAddGroup.map_comp, skeleton_inverse_left,
    GrothendieckAddGroup.map_id]

private theorem groth_inverse_right :
    (grothMap E.functor).comp (grothMap E.inverse) =
      AddMonoidHom.id (GrothendieckAddGroup (Skeleton D)) := by
  change (GrothendieckAddGroup.map
      (Skeleton.mapAddMonoidHom (F := E.functor))).comp
      (GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.inverse))) = _
  rw [← GrothendieckAddGroup.map_comp, skeleton_inverse_right,
    GrothendieckAddGroup.map_id]

/-- Both functions are fixed by F and the original inverse G, not by a chosen classifier. -/
public def grothEquiv :
    GrothendieckAddGroup (Skeleton C) ≃+ GrothendieckAddGroup (Skeleton D) where
  toFun := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.functor))
  invFun := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.inverse))
  left_inv x := by
    exact DFunLike.congr_fun (groth_inverse_left E) x
  right_inv x := by
    exact DFunLike.congr_fun (groth_inverse_right E) x
  map_add' := (GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.functor))).map_add

/-- The induced Grothendieck equivalence uses the original additive functor on every class. -/
public theorem grothEquiv_apply (x : GrothendieckAddGroup (Skeleton C)) :
    grothEquiv E x = GrothendieckAddGroup.map
      (Skeleton.mapAddMonoidHom (F := E.functor)) x := rfl

/-- The inverse Grothendieck function is fixed by the original equivalence inverse. -/
public theorem grothEquiv_symm_apply (x : GrothendieckAddGroup (Skeleton D)) :
    (grothEquiv E).symm x = GrothendieckAddGroup.map
      (Skeleton.mapAddMonoidHom (F := E.inverse)) x := rfl

end GrothEquivalence

end CategoryTheory.SInverseS



namespace CategoryTheory.SInverseS

open Algebra

-- Public types use the existing Mathlib preservation recipe instead of this private instance.
attribute [-instance] preservesBinaryBiproduct

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

section FunctorCharacteristic

variable {K : Type uK} [Category.{vK} K] [Preadditive K]
  [HasZeroObject K] [HasBinaryBiproducts K]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
variable (α : F ≅ G) (H : D ⥤ K) [H.Additive]

/-- The actual raw and quotient maps, their original relation witnesses, and the canonical
natural-isomorphism, identity and composition components of additive Pair transport. -/
public theorem pairFunctor_characteristic :
    letI (X Y : C) : PreservesBinaryBiproduct X Y F :=
      preservesBinaryBiproduct_of_preservesBiproduct F X Y
    (∀ X : Pair C, (pairFunctor F).obj X = (⟨F.obj X.fst, F.obj X.snd⟩ : Pair D)) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      (pairFunctor F).map (Hom.mk f) = Hom.mk (mapRawHom F f)) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      (mapRawHom F f).stabilizer = F.obj f.stabilizer) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      (mapRawHom F f).hom₁ =
        (F.mapBiprod f.stabilizer X.fst).symm ≪≫ F.mapIso f.hom₁) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      (mapRawHom F f).hom₂ =
        (F.mapBiprod f.stabilizer X.snd).symm ≪≫ F.mapIso f.hom₂) ∧
    (∀ {X Y : Pair C} (f g : RawHom X Y),
      f.Rel g → (mapRawHom F f).Rel (mapRawHom F g)) ∧
    (∀ X : Pair C,
      (mapRawHom F (RawHom.id X)).Rel (RawHom.id ((pairFunctor F).obj X))) ∧
    (∀ {X Y Z : Pair C} (f : RawHom X Y) (g : RawHom Y Z),
      (mapRawHom F (f.comp g)).Rel ((mapRawHom F f).comp (mapRawHom F g))) ∧
    (∀ X : Pair C, (pairFunctorNatIso F G α).app X =
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨F.obj X.fst⟩) (y := ⟨G.obj X.fst⟩) (α.app X.fst)).prod
          (Core.isoMk (x := ⟨F.obj X.snd⟩) (y := ⟨G.obj X.snd⟩) (α.app X.snd)))) ∧
    (∀ X : Pair C, (pairFunctorIdentity (C := C)).app X = Iso.refl X) ∧
    (∀ X : Pair C, (pairFunctorComposite F H).app X =
      Iso.refl ((pairFunctor (F ⋙ H)).obj X)) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y), mapRawHom (𝟭 C) f = f) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      mapRawHom (F ⋙ H) f = mapRawHom H (mapRawHom F f)) := by
  let (X Y : C) : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBiproduct F X Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    rfl
  · intro X Y f
    rfl
  · intro X Y f
    rfl
  · intro X Y f
    rfl
  · intro X Y f
    rfl
  · intro X Y f g h
    exact mapRawHom_rel F h
  · intro X
    exact mapRawHom_id_rel F X
  · intro X Y Z f g
    exact mapRawHom_comp_rel F f g
  · intro X
    rfl
  · intro X
    rfl
  · intro X
    rfl
  · intro X Y f
    exact mapRawHom_identity f
  · intro X Y f
    exact mapRawHom_composite F H f

end FunctorCharacteristic

section PairEquivalenceCharacteristic

variable (E : C ≌ D) [E.functor.Additive]

/-- Both actual functors and the normalized unit and counit of the induced Pair equivalence,
with their unrestricted object and raw-map formulas. -/
public theorem pairEquivalence_characteristic :
    let η₀ := (pairFunctorIdentity (C := C)).symm ≪≫
      pairFunctorNatIso (𝟭 C) (E.functor ⋙ E.inverse) E.unitIso ≪≫
        pairFunctorComposite E.functor E.inverse
    let ε₀ := (pairFunctorComposite E.inverse E.functor).symm ≪≫
      pairFunctorNatIso (E.inverse ⋙ E.functor) (𝟭 D) E.counitIso ≪≫
        pairFunctorIdentity (C := D)
    (pairEquivalence E).functor = pairFunctor E.functor ∧
    (pairEquivalence E).inverse = pairFunctor E.inverse ∧
    (pairEquivalence E).unitIso = Equivalence.adjointifyη η₀ ε₀ ∧
    (pairEquivalence E).counitIso = ε₀ ∧
    (∀ X : Pair C, (pairEquivalence E).functor.obj X =
      (⟨E.functor.obj X.fst, E.functor.obj X.snd⟩ : Pair D)) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      (pairEquivalence E).functor.map (Hom.mk f) = Hom.mk (mapRawHom E.functor f)) ∧
    (∀ X : Pair D, (pairEquivalence E).inverse.obj X =
      (⟨E.inverse.obj X.fst, E.inverse.obj X.snd⟩ : Pair C)) ∧
    (∀ {X Y : Pair D} (f : RawHom X Y),
      (pairEquivalence E).inverse.map (Hom.mk f) = Hom.mk (mapRawHom E.inverse f)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro X
    rfl
  · intro X Y f
    rfl
  · intro X
    rfl
  · intro X Y f
    rfl

end PairEquivalenceCharacteristic

section ForwardCharacteristics

variable (F : C ⥤ D) [F.Additive]

/-- Canonical Core, genuine negative Core, swap, zero and both translation comparisons,
including the original unflattened translate-to-zero and diagonal-add arrows. -/
public theorem coreTranslation_characteristic :
    letI (X Y : C) : PreservesBinaryBiproduct X Y F :=
      preservesBinaryBiproduct_of_preservesBiproduct F X Y
    (∀ {X Y : Core C × Core C} (f : X ⟶ Y),
      (pairFunctor F).map ((corePairInclusion (C := C)).map f) =
        (corePairInclusion (C := D)).map ((F.core.prod F.core).map f)) ∧
    (∀ X : Core C × Core C, (corePairIso F).app X =
      Iso.refl ((corePairInclusion (C := C) ⋙ pairFunctor F).obj X)) ∧
    (∀ X : Core C, (positiveCoreIso F).app X =
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨F.obj X.of⟩) (y := ⟨F.obj X.of⟩)
          (Iso.refl (F.obj X.of))).prod
          (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject))) ∧
    (∀ X : Core C, (negativeCoreIso F).app X =
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
          (Core.isoMk (x := ⟨F.obj X.of⟩) (y := ⟨F.obj X.of⟩)
            (Iso.refl (F.obj X.of))))) ∧
    (swapFunctor (C := C) ⋙ pairFunctor F = pairFunctor F ⋙ swapFunctor (C := D)) ∧
    (∀ {X Y : Pair C} (f : RawHom X Y),
      mapRawHom F f.swap = (mapRawHom F f).swap) ∧
    (∀ (A : C) (X : Pair C), (translateFirstIso F A).app X =
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨F.obj (A ⊞ X.fst)⟩)
          (y := ⟨F.obj A ⊞ F.obj X.fst⟩) (F.mapBiprod A X.fst)).prod
          (Core.isoMk (x := ⟨F.obj X.snd⟩) (y := ⟨F.obj X.snd⟩)
            (Iso.refl (F.obj X.snd))))) ∧
    (∀ (A : C) (X : Pair C), (translateSecondIso F A).app X =
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨F.obj X.fst⟩) (y := ⟨F.obj X.fst⟩)
          (Iso.refl (F.obj X.fst))).prod
          (Core.isoMk (x := ⟨F.obj (A ⊞ X.snd)⟩)
            (y := ⟨F.obj A ⊞ F.obj X.snd⟩) (F.mapBiprod A X.snd)))) ∧
    (zeroPairIso F = (corePairInclusion (C := D)).mapIso
      ((Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject).prod
        (Core.isoMk (x := ⟨F.obj (0 : C)⟩) (y := ⟨(0 : D)⟩) F.mapZeroObject))) ∧
    ((zeroPairIso F).hom = Hom.mk
      ({ stabilizer := (0 : D)
         hom₁ := (isoZeroBiprod (isZero_zero D)).symm ≪≫ F.mapZeroObject
         hom₂ := (isoZeroBiprod (isZero_zero D)).symm ≪≫ F.mapZeroObject } :
        RawHom ((pairFunctor F).obj (⟨0, 0⟩ : Pair C)) ⟨0, 0⟩)) ∧
    (∀ X Y : Pair C, (toZeroIso F X).app Y =
      (translateFirstIso F X.snd).app ((translateSecondFunctor X.fst).obj Y) ≪≫
        (translateFirstFunctor (F.obj X.snd)).mapIso ((translateSecondIso F X.fst).app Y)) ∧
    (∀ X Y : Pair C, (toZeroIso F X).app Y =
      (corePairInclusion (C := D)).mapIso
        ((Core.isoMk (x := ⟨F.obj (X.snd ⊞ Y.fst)⟩)
          (y := ⟨F.obj X.snd ⊞ F.obj Y.fst⟩) (F.mapBiprod X.snd Y.fst)).prod
          (Core.isoMk (x := ⟨F.obj (X.fst ⊞ Y.snd)⟩)
            (y := ⟨F.obj (X.fst ⊞ Y.snd)⟩) (Iso.refl _))) ≪≫
        (translateFirstFunctor (F.obj X.snd)).mapIso
          ((corePairInclusion (C := D)).mapIso
            ((Core.isoMk (x := ⟨F.obj Y.fst⟩) (y := ⟨F.obj Y.fst⟩) (Iso.refl _)).prod
              (Core.isoMk (x := ⟨F.obj (X.fst ⊞ Y.snd)⟩)
                (y := ⟨F.obj X.fst ⊞ F.obj Y.snd⟩) (F.mapBiprod X.fst Y.snd))))) ∧
    (∀ (A : C) (X : Pair C),
      (pairFunctor F).map (diagonalAddHom A X) ≫
        ((corePairInclusion (C := D)).mapIso
          ((Core.isoMk (x := ⟨F.obj (A ⊞ X.fst)⟩)
            (y := ⟨F.obj A ⊞ F.obj X.fst⟩) (F.mapBiprod A X.fst)).prod
            (Core.isoMk (x := ⟨F.obj (A ⊞ X.snd)⟩)
              (y := ⟨F.obj A ⊞ F.obj X.snd⟩) (F.mapBiprod A X.snd)))).hom =
        diagonalAddHom (F.obj A) ((pairFunctor F).obj X)) := by
  let (X Y : C) : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBiproduct F X Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f
    exact corePair_map F f
  · intro X
    rfl
  · intro X
    rfl
  · intro X
    rfl
  · exact pairFunctor_swap F
  · intro X Y f
    rfl
  · intro A X
    rfl
  · intro A X
    rfl
  · rfl
  · rfl
  · intro X Y
    exact toZeroIso_app F X Y
  · intro X Y
    exact toZeroIso_app_coordinates F X Y
  · intro A X
    exact diagonal_map F A X

/-- The fixed Grothendieck map describes every categorical component, both Core signs,
swap and both translations for an arbitrary additive functor. -/
public theorem components_characteristic :
    let kF := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := F))
    (∀ X : Pair C, kF X.difference = ((pairFunctor F).obj X).difference) ∧
    (∀ a : ConnectedComponents (Pair C),
      connectedComponentsToGrothendieck ((pairFunctor F).mapConnectedComponents a) =
        kF (connectedComponentsToGrothendieck a)) ∧
    (∀ X : Core C, connectedComponentsToGrothendieck
      ((pairFunctor F).mapConnectedComponents
        (ConnectedComponents.mk ((coreInclusion (C := C)).obj X))) =
      GrothendieckAddGroup.of (toSkeleton (F.obj X.of))) ∧
    (∀ X : Core C, connectedComponentsToGrothendieck
      ((pairFunctor F).mapConnectedComponents
        (ConnectedComponents.mk ((negativeCoreInclusion (C := C)).obj X))) =
      -GrothendieckAddGroup.of (toSkeleton (F.obj X.of))) ∧
    (∀ a : ConnectedComponents (Pair C), connectedComponentsToGrothendieck
      ((swapFunctor (C := D)).mapConnectedComponents
        ((pairFunctor F).mapConnectedComponents a)) =
      -kF (connectedComponentsToGrothendieck a)) ∧
    (∀ (A : C) (a : ConnectedComponents (Pair C)), connectedComponentsToGrothendieck
      ((translateFirstFunctor (F.obj A)).mapConnectedComponents
        ((pairFunctor F).mapConnectedComponents a)) =
      GrothendieckAddGroup.of (toSkeleton (F.obj A)) +
        kF (connectedComponentsToGrothendieck a)) ∧
    (∀ (A : C) (a : ConnectedComponents (Pair C)), connectedComponentsToGrothendieck
      ((translateSecondFunctor (F.obj A)).mapConnectedComponents
        ((pairFunctor F).mapConnectedComponents a)) =
      kF (connectedComponentsToGrothendieck a) -
        GrothendieckAddGroup.of (toSkeleton (F.obj A))) ∧
    (∀ (X : Pair C) (a : ConnectedComponents (Pair C)), connectedComponentsToGrothendieck
      ((translateToZeroFunctor ((pairFunctor F).obj X)).mapConnectedComponents
        ((pairFunctor F).mapConnectedComponents a)) =
      kF (connectedComponentsToGrothendieck a - X.difference)) ∧
    (∀ (X : Pair C) (a : ConnectedComponents (Pair C)),
      (translateToZeroFunctor ((pairFunctor F).obj X)).mapConnectedComponents
          ((pairFunctor F).mapConnectedComponents a) =
        (pairFunctor F).mapConnectedComponents
          ((translateToZeroFunctor X).mapConnectedComponents a)) ∧
    (∀ X : Pair C, connectedComponentsToGrothendieck
      ((translateToZeroFunctor ((pairFunctor F).obj X)).mapConnectedComponents
        ((pairFunctor F).mapConnectedComponents (ConnectedComponents.mk X))) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    exact difference_map F X
  · intro a
    exact components_map F a
  · intro X
    exact components_positive F X
  · intro X
    exact components_negative F X
  · intro a
    exact components_swap F a
  · intro A a
    exact components_first F A a
  · intro A a
    exact components_second F A a
  · intro X a
    exact components_toZero F X a
  · intro X a
    exact components_toZero_commutes F X a
  · intro X
    exact components_toZero_selected F X

end ForwardCharacteristics

section GrothEquivalenceCharacteristic

variable (E : C ≌ D) [E.functor.Additive]

/-- The original equivalence unit and counit give the fixed skeleton and Grothendieck
inverse maps, without choosing a replacement classifier. -/
public theorem grothEquivalence_characteristic :
    let kF := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.functor))
    let kG := GrothendieckAddGroup.map (Skeleton.mapAddMonoidHom (F := E.inverse))
    ((Skeleton.mapAddMonoidHom (F := E.inverse)).comp
      (Skeleton.mapAddMonoidHom (F := E.functor)) = AddMonoidHom.id (Skeleton C)) ∧
    ((Skeleton.mapAddMonoidHom (F := E.functor)).comp
      (Skeleton.mapAddMonoidHom (F := E.inverse)) = AddMonoidHom.id (Skeleton D)) ∧
    (kG.comp kF = AddMonoidHom.id (GrothendieckAddGroup (Skeleton C))) ∧
    (kF.comp kG = AddMonoidHom.id (GrothendieckAddGroup (Skeleton D))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact skeleton_inverse_left E
  · exact skeleton_inverse_right E
  · exact groth_inverse_left E
  · exact groth_inverse_right E

end GrothEquivalenceCharacteristic

end CategoryTheory.SInverseS


namespace CategoryTheory.SInverseS

section OriginalCanonicalRawCoordinateValues

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mapBiprodOriginalStabilizerRelationComputed {s t X Y : C}
    (e : s ≅ t) (f : s ⊞ X ≅ Y) (g : t ⊞ X ≅ Y)
    (h : (stabilizerIso e X).trans g = f) :
    letI (A B : C) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    (stabilizerIso (F.mapIso e) (F.obj X)).hom ≫
        ((F.mapBiprod t X).symm.trans (F.mapIso g)).hom =
      ((F.mapBiprod s X).symm.trans (F.mapIso f)).hom := by
  let (A B : C) : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  exact map_relation_coordinate F e f g h

omit [HasZeroObject C] [HasZeroObject D] in
/-- The canonical comparison preserves the original relation with the same mapped stabilizer. -/
public theorem mapBiprod_original_stabilizer_relation {s t X Y : C}
    (e : s ≅ t) (f : s ⊞ X ≅ Y) (g : t ⊞ X ≅ Y)
    (h : (stabilizerIso e X).trans g = f) :
    letI (A B : C) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    (stabilizerIso (F.mapIso e) (F.obj X)).hom ≫
        ((F.mapBiprod t X).symm.trans (F.mapIso g)).hom =
      ((F.mapBiprod s X).symm.trans (F.mapIso f)).hom :=
  mapBiprodOriginalStabilizerRelationComputed F e f g h

private theorem mapBiprodOriginalZeroUnitComputed (X : C) :
    letI (A B : C) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    (stabilizerIso F.mapZeroObject (F.obj X)).trans
        (isoZeroBiprod (X := (0 : D)) (Y := F.obj X) (isZero_zero D)).symm =
      (F.mapBiprod (0 : C) X).symm.trans
        (F.mapIso (isoZeroBiprod (X := (0 : C)) (Y := X) (isZero_zero C)).symm) := by
  let (A B : C) : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  exact biprodIso_zero_unit F X

/-- The original zero unit is preserved through canonical mapZeroObject and mapBiprod. -/
public theorem mapBiprod_original_zero_unit (X : C) :
    letI (A B : C) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    (stabilizerIso F.mapZeroObject (F.obj X)).trans
        (isoZeroBiprod (X := (0 : D)) (Y := F.obj X) (isZero_zero D)).symm =
      (F.mapBiprod (0 : C) X).symm.trans
        (F.mapIso (isoZeroBiprod (X := (0 : C)) (Y := X) (isZero_zero C)).symm) :=
  mapBiprodOriginalZeroUnitComputed F X

omit [HasZeroObject C] [HasZeroObject D] in
private theorem mapBiprodOriginalCompositionCoordinateComputed {s t X Y Z : C}
    (f : s ⊞ X ≅ Y) (g : t ⊞ Y ≅ Z) :
    letI (A B : C) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    biprod.map (F.mapBiprod t s).hom (𝟙 (F.obj X)) ≫
        (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
        biprod.map (𝟙 (F.obj t))
          ((F.mapBiprod s X).inv ≫ F.map f.hom) ≫
        (F.mapBiprod t Y).inv ≫ F.map g.hom =
      (F.mapBiprod (t ⊞ s) X).inv ≫ F.map
        ((biprod.associator t s X).hom ≫
          biprod.map (𝟙 t) f.hom ≫ g.hom) := by
  let (A B : C) : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  exact map_composition_coordinate F f g

omit [HasZeroObject C] [HasZeroObject D] in
/-- The whole original composition coordinate retains its later-then-earlier stabilizer. -/
public theorem mapBiprod_original_composition_coordinate {s t X Y Z : C}
    (f : s ⊞ X ≅ Y) (g : t ⊞ Y ≅ Z) :
    letI (A B : C) : PreservesBinaryBiproduct A B F :=
      preservesBinaryBiproduct_of_preservesBiproduct F A B
    biprod.map (F.mapBiprod t s).hom (𝟙 (F.obj X)) ≫
        (biprod.associator (F.obj t) (F.obj s) (F.obj X)).hom ≫
        biprod.map (𝟙 (F.obj t))
          ((F.mapBiprod s X).inv ≫ F.map f.hom) ≫
        (F.mapBiprod t Y).inv ≫ F.map g.hom =
      (F.mapBiprod (t ⊞ s) X).inv ≫ F.map
        ((biprod.associator t s X).hom ≫
          biprod.map (𝟙 t) f.hom ≫ g.hom) :=
  mapBiprodOriginalCompositionCoordinateComputed F f g

end OriginalCanonicalRawCoordinateValues

end CategoryTheory.SInverseS
