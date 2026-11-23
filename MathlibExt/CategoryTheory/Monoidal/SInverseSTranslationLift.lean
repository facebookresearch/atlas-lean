/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslation
public import MathlibExt.CategoryTheory.FiberedCategory.Cofibered

/-!
# Canonical lifts for the additive S⁻¹S translation projection

Given an object `(X₁,X₂)` of additive `S⁻¹S` and a translation arrow out of
`X₁`, choose its quotient representative `(s, s ⊞ X₁ ≅ Y₁)`.  The canonical
lift has target `(Y₁, s ⊞ X₂)` and uses the identity in the second
coordinate.

This file proves that the constructed total arrow lies over the supplied
translation arrow and satisfies the strongly cocartesian universal property.
Packaging the projection itself as a cofibered functor is a separate gate.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

namespace Translation

/-- Chosen raw representative of a quotient translation arrow. -/
noncomputable def representative {X Y : Translation C} (f : X ⟶ Y) :
    RawHom X Y :=
  Quotient.out f

@[simp]
theorem mk_representative {X Y : Translation C} (f : X ⟶ Y) :
    Hom.mk (representative f) = f :=
  Quotient.out_eq f

end Translation

/-- Target object of the canonical lift of a translation arrow. -/
noncomputable def translationLiftObj (X : Pair C) {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) : Pair C :=
  ⟨Y.of, (Translation.representative f).stabilizer ⊞ X.snd⟩

@[simp]
theorem translationLiftObj_fst (X : Pair C) {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    (translationLiftObj X f).fst = Y.of :=
  rfl

@[simp]
theorem translationProjection_obj_liftObj (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    (translationProjection (C := C)).obj (translationLiftObj X f) = Y := by
  cases Y
  rfl

/-- Raw total arrow underlying the canonical lift. -/
noncomputable def translationLiftRawHom (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    RawHom X (translationLiftObj X f) where
  stabilizer := (Translation.representative f).stabilizer
  hom₁ := (Translation.representative f).hom
  hom₂ := Iso.refl _

/-- Canonical total arrow lifting a translation arrow. -/
noncomputable def translationLiftHom (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    X ⟶ translationLiftObj X f :=
  Hom.mk (translationLiftRawHom X f)

@[simp]
theorem translationProjection_map_liftHom (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    (translationProjection (C := C)).map (translationLiftHom X f) = f :=
  Translation.mk_representative f

/-- The canonical total arrow is a lift of the supplied base arrow. -/
noncomputable instance translationLiftHom_isHomLift (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    (translationProjection (C := C)).IsHomLift f
      (translationLiftHom X f) := by
  rcases Y with ⟨Y⟩
  apply IsHomLift.of_commsq
    (translationProjection (C := C)) f (translationLiftHom X f)
      rfl rfl
  rw [translationProjection_map_liftHom]
  change f ≫ 𝟙 _ = 𝟙 _ ≫ f
  exact (Category.comp_id f).trans (Category.id_comp f).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any total arrow over a composite base arrow factors through the
canonical lift.  This is the existence half of the cocartesian universal
property. -/
theorem translationLift_exists_factor (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y)
    {Z : Pair C}
    (g : Y ⟶ (translationProjection (C := C)).obj Z)
    (ψ : X ⟶ Z)
    [(translationProjection (C := C)).IsHomLift (f ≫ g) ψ] :
    ∃ χ : translationLiftObj X f ⟶ Z,
      (translationProjection (C := C)).map χ = g ∧
        translationLiftHom X f ≫ χ = ψ := by
  let q := Translation.representative f
  let t := Translation.representative g
  let r := Hom.representative ψ
  have hbase := IsHomLift.eq_of_isHomLift
    (translationProjection (C := C)) (f ≫ g) ψ
  change Translation.Hom.comp f g = Hom.toTranslation ψ at hbase
  rw [← Translation.mk_representative f,
    ← Translation.mk_representative g,
    ← Hom.mk_representative ψ] at hbase
  change Translation.Hom.mk (q.comp t) =
    Translation.Hom.mk r.toTranslation at hbase
  obtain ⟨e, he⟩ := Quotient.exact hbase
  let χraw : RawHom (translationLiftObj X f) Z :=
    { stabilizer := t.stabilizer
      hom₁ := t.hom
      hom₂ := (biprod.associator t.stabilizer q.stabilizer X.snd).symm.trans
        ((SInverseS.stabilizerIso e X.snd).trans r.hom₂) }
  let χ : translationLiftObj X f ⟶ Z := Hom.mk χraw
  refine ⟨χ, ?_, ?_⟩
  · change Translation.Hom.mk t = g
    exact Translation.mk_representative g
  · rw [← Hom.mk_representative ψ]
    apply Quotient.sound
    refine ⟨e, ?_, ?_⟩
    · change (SInverseS.stabilizerIso e X.fst).trans r.hom₁ =
        (biprod.associator t.stabilizer q.stabilizer X.fst).trans
          ((biprod.mapIso (Iso.refl t.stabilizer) q.hom).trans t.hom)
      change (SInverseS.stabilizerIso e X.fst).trans r.hom₁ =
        (biprod.associator t.stabilizer q.stabilizer X.fst).trans
          ((biprod.mapIso (Iso.refl t.stabilizer) q.hom).trans t.hom) at he
      exact he
    · apply Iso.ext
      dsimp [q, t, r, χraw, translationLiftRawHom, RawHom.comp,
        SInverseS.stabilizerIso]
      have hid : biprod.map
          (𝟙 (Translation.representative g).stabilizer)
          (𝟙 ((Translation.representative f).stabilizer ⊞ X.snd)) =
          𝟙 _ := by
        apply biprod.hom_ext <;> simp
      have hidIso : biprod.mapIso
          (Iso.refl (Translation.representative g).stabilizer)
          (Iso.refl
            ((Translation.representative f).stabilizer ⊞ X.snd)) =
          Iso.refl _ := by
        apply Iso.ext
        exact hid
      rw [hidIso, Iso.refl_hom, Category.id_comp,
        Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A factor through a canonical translation lift is determined by its
projection and its composite with the lift. -/
theorem translationLift_cancel (X : Pair C)
    {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y)
    {Z : Pair C}
    (chi chi' : translationLiftObj X f ⟶ Z)
    (hbase : (translationProjection (C := C)).map chi =
      (translationProjection (C := C)).map chi')
    (hcomp : translationLiftHom X f ≫ chi =
      translationLiftHom X f ≫ chi') :
    chi = chi' := by
  let q := Translation.representative f
  let a := Hom.representative chi
  let b := Hom.representative chi'
  rw [← Hom.mk_representative chi,
    ← Hom.mk_representative chi'] at hbase
  change Translation.Hom.mk a.toTranslation =
    Translation.Hom.mk b.toTranslation at hbase
  obtain ⟨d, hd⟩ := Quotient.exact hbase
  change a.stabilizer ≅ b.stabilizer at d
  change (stabilizerIso d Y.of).trans b.hom₁ = a.hom₁ at hd
  rw [← Hom.mk_representative chi,
    ← Hom.mk_representative chi'] at hcomp
  change Hom.mk ((translationLiftRawHom X f).comp a) =
    Hom.mk ((translationLiftRawHom X f).comp b) at hcomp
  obtain ⟨e, he₁, he₂⟩ := Quotient.exact hcomp
  change (a.stabilizer ⊞ q.stabilizer) ≅
    (b.stabilizer ⊞ q.stabilizer) at e
  have hcanonical₁ :
      (stabilizerIso (biprod.mapIso d (Iso.refl q.stabilizer)) X.fst).trans
          ((translationLiftRawHom X f).comp b).hom₁ =
        ((translationLiftRawHom X f).comp a).hom₁ := by
    apply Iso.ext
    have h := rawComp_changeStabilizer_hom
      (X := X.fst) (𝟙 q.stabilizer) d.hom q.hom.hom b.hom₁.hom
    have hdHom := congrArg Iso.hom hd
    change biprod.map d.hom (𝟙 Y.of) ≫ b.hom₁.hom = a.hom₁.hom at hdHom
    rw [hdHom] at h
    have hid : biprod.map (𝟙 q.stabilizer) (𝟙 X.fst) = 𝟙 _ := by
      apply biprod.hom_ext <;> simp
    rw [hid, Category.id_comp] at h
    simpa [q, RawHom.comp, translationLiftRawHom, stabilizerIso,
      Category.assoc] using h
  have heq : e = biprod.mapIso d (Iso.refl q.stabilizer) := by
    apply Iso.ext
    change e.hom = biprod.map d.hom (𝟙 q.stabilizer)
    have houter : stabilizerIso e X.fst =
        stabilizerIso (biprod.mapIso d (Iso.refl q.stabilizer)) X.fst := by
      apply Iso.ext
      apply (cancel_mono
        ((translationLiftRawHom X f).comp b).hom₁.hom).1
      exact (congrArg Iso.hom he₁).trans
        (congrArg Iso.hom hcanonical₁).symm
    have houterHom := congrArg Iso.hom houter
    change biprod.map e.hom (𝟙 X.fst) =
      biprod.map (biprod.map d.hom (𝟙 q.stabilizer)) (𝟙 X.fst) at houterHom
    have hleft := congrArg
      (fun k => (biprod.inl :
          (a.stabilizer ⊞ q.stabilizer) ⟶
            (a.stabilizer ⊞ q.stabilizer) ⊞ X.fst) ≫ k)
      houterHom
    apply (cancel_mono (biprod.inl :
      (b.stabilizer ⊞ q.stabilizer) ⟶
        (b.stabilizer ⊞ q.stabilizer) ⊞ X.fst)).1
    simpa only [biprod.inl_map] using hleft
  rw [heq] at he₂
  rw [← Hom.mk_representative chi,
    ← Hom.mk_representative chi']
  apply Quotient.sound
  refine ⟨d, hd, ?_⟩
  apply Iso.ext
  change biprod.map d.hom (𝟙 (q.stabilizer ⊞ X.snd)) ≫
    b.hom₂.hom = a.hom₂.hom
  have h := rawComp_changeStabilizer_hom
    (X := X.snd) (𝟙 q.stabilizer) d.hom
      (𝟙 (q.stabilizer ⊞ X.snd)) b.hom₂.hom
  have he₂Hom := congrArg Iso.hom he₂
  change
    biprod.map (biprod.map d.hom (𝟙 q.stabilizer)) (𝟙 X.snd) ≫
          (biprod.associator b.stabilizer q.stabilizer X.snd).hom ≫
          biprod.map (𝟙 b.stabilizer) (𝟙 (q.stabilizer ⊞ X.snd)) ≫
          b.hom₂.hom =
        (biprod.associator a.stabilizer q.stabilizer X.snd).hom ≫
          biprod.map (𝟙 a.stabilizer) (𝟙 (q.stabilizer ⊞ X.snd)) ≫
          a.hom₂.hom at he₂Hom
  rw [he₂Hom] at h
  have hidq : biprod.map (𝟙 q.stabilizer) (𝟙 X.snd) = 𝟙 _ := by
    apply biprod.hom_ext <;> simp
  have hida : biprod.map (𝟙 a.stabilizer)
      (𝟙 (q.stabilizer ⊞ X.snd)) = 𝟙 _ := by
    apply biprod.hom_ext <;> simp
  simp only [hidq, hida, Category.id_comp,
    Category.comp_id] at h
  exact ((cancel_epi
    (biprod.associator a.stabilizer q.stabilizer X.snd).hom).1 h).symm

/-- The canonical lift of a translation arrow is strongly cocartesian. -/
noncomputable instance translationLiftHom_isStronglyCocartesian
    (X : Pair C) {Y : Translation C}
    (f : (translationProjection (C := C)).obj X ⟶ Y) :
    (translationProjection (C := C)).IsStronglyCocartesian f
      (translationLiftHom X f) where
  universal_property' {b'} g psi hpsi := by
    rcases Y with ⟨Y⟩
    let _ : (translationProjection (C := C)).IsHomLift (f ≫ g) psi :=
      hpsi
    obtain ⟨chi, hmap, hcomp⟩ :=
      translationLift_exists_factor X f g psi
    let _ : (translationProjection (C := C)).IsHomLift g chi :=
      hmap ▸ IsHomLift.map (translationProjection (C := C)) chi
    refine ⟨chi, ⟨inferInstance, hcomp⟩, ?_⟩
    rintro chi' ⟨hchi', hcomp'⟩
    let _ : (translationProjection (C := C)).IsHomLift g chi' := hchi'
    have hmap' : (translationProjection (C := C)).map chi' =
        (translationProjection (C := C)).map chi := by
      rw [IsHomLift.fac' (translationProjection (C := C)) g chi',
        IsHomLift.fac' (translationProjection (C := C)) g chi]
    exact translationLift_cancel X f chi' chi hmap'
      (hcomp'.trans hcomp.symm)

/-- The additive translation projection is a cofibered functor. -/
noncomputable instance translationProjection_isCofibered :
    (translationProjection (C := C)).IsCofibered where
  exists_isStronglyCocartesian' {a} {_T} f :=
    ⟨translationLiftObj a f, translationLiftHom a f, inferInstance⟩

end SInverseS
end CategoryTheory

end
