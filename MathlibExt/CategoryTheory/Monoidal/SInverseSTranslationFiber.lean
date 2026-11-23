/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslation
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Core objects in fibers of the additive S⁻¹S translation projection

For a selected base object `B`, an object `X` of `Core(C)` determines the
pair `(B,X)` in the strict fiber of
`S⁻¹S(C) ⟶ ⟨S,S⟩`.  A core isomorphism acts in the second coordinate while
the first coordinate remains the identity.

This file packages the resulting functor from `Core(C)` into the strict
fiber and proves that it is an equivalence.  Fullness uses the base identity
to cancel the stabilizer of a fiber arrow; essential surjectivity identifies
the first coordinate of a fiber object with the chosen base object.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The strict fiber of the translation projection over a wrapped core
object. -/
abbrev TranslationFiber (B : Core C) :=
  (translationProjection (C := C)).Fiber
    (⟨B.of⟩ : Translation C)

/-- Pair a fixed first core object with a varying second core object. -/
noncomputable def coreFiberPair (B : Core C) : Core C ⥤ Pair C :=
  (((Functor.const (Core C)).obj B).prod' (𝟭 (Core C))) ⋙
    corePairInclusion

@[simp]
theorem translationProjection_map_coreFiberPair (B : Core C)
    {X Y : Core C} (f : X ⟶ Y) :
    (translationProjection (C := C)).map
        ((coreFiberPair B).map f) =
      𝟙 ((translationProjection (C := C)).obj
        ((coreFiberPair B).obj X)) := by
  change Translation.Hom.mk
      { stabilizer := 0
        hom := (isoZeroBiprod (isZero_zero C)).symm.trans
          (Iso.refl B.of) } =
    Translation.Hom.id ⟨B.of⟩
  apply Quotient.sound
  refine ⟨Iso.refl (0 : C), ?_⟩
  dsimp only [Translation.RawHom.id]
  rw [stabilizerIso_refl, Iso.refl_trans, Iso.trans_refl]

/-- The canonical functor from the core into the strict fiber over `B`. -/
noncomputable def coreToTranslationFiber (B : Core C) :
    Core C ⥤ TranslationFiber B where
  obj X := ⟨(coreFiberPair B).obj X, rfl⟩
  map {X Y} f := by
    let φ := (coreFiberPair B).map f
    have hφ : (translationProjection (C := C)).map φ =
        𝟙 (⟨B.of⟩ : Translation C) :=
      translationProjection_map_coreFiberPair B f
    letI : (translationProjection (C := C)).IsHomLift
        ((translationProjection (C := C)).map φ) φ := inferInstance
    haveI : (translationProjection (C := C)).IsHomLift
        (𝟙 (⟨B.of⟩ : Translation C)) φ := by
      rwa [hφ] at this
    exact ⟨φ, inferInstance⟩
  map_id X := by
    apply Functor.Fiber.hom_ext
    exact (coreFiberPair B).map_id X
  map_comp f g := by
    apply Functor.Fiber.hom_ext
    exact (coreFiberPair B).map_comp f g

@[simp]
theorem coreToTranslationFiber_obj_val (B X : Core C) :
    ((coreToTranslationFiber B).obj X).1 = ⟨B.of, X.of⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The core-to-fiber functor is faithful. -/
noncomputable instance coreToTranslationFiber_faithful (B : Core C) :
    (coreToTranslationFiber B).Faithful where
  map_injective {X Y} f g h := by
    apply Core.hom_ext
    let pf : (B, X) ⟶ (B, Y) := (𝟙 B, f)
    let pg : (B, X) ⟶ (B, Y) := (𝟙 B, g)
    have hq :
        Hom.mk (RawHom.ofCorePair pf) =
          Hom.mk (RawHom.ofCorePair pg) := by
      exact congrArg Subtype.val h
    obtain ⟨e, _, he₂⟩ := Quotient.exact hq
    have he : e = Iso.refl (0 : C) := by
      apply Iso.ext
      exact (isZero_zero C).eq_of_src _ _
    rw [he, stabilizerIso_refl, Iso.refl_trans] at he₂
    have hh := congrArg Iso.hom he₂
    dsimp only [pf, pg, RawHom.ofCorePair, Iso.trans_hom] at hh
    rw [cancel_epi] at hh
    exact hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The core-to-fiber functor is full. -/
noncomputable instance coreToTranslationFiber_full (B : Core C) :
    (coreToTranslationFiber B).Full where
  map_surjective {X Y} φ := by
    let r := Hom.representative φ.1
    let _ : (translationProjection (C := C)).IsHomLift
        (𝟙 (⟨B.of⟩ : Translation C)) φ.1 := φ.2
    have hbase := IsHomLift.eq_of_isHomLift
      (translationProjection (C := C))
      (𝟙 (⟨B.of⟩ : Translation C)) φ.1
    change Translation.Hom.id ⟨B.of⟩ = Hom.toTranslation φ.1 at hbase
    rw [← Hom.mk_representative φ.1] at hbase
    change Translation.Hom.mk (Translation.RawHom.id ⟨B.of⟩) =
      Translation.Hom.mk r.toTranslation at hbase
    obtain ⟨e, he⟩ := Quotient.exact hbase.symm
    change r.stabilizer ≅ 0 at e
    change (stabilizerIso e B.of).trans
      (isoZeroBiprod (isZero_zero C)).symm = r.hom₁ at he
    let fIso : X.of ≅ Y.of :=
      (isoZeroBiprod (isZero_zero C)).trans
        ((stabilizerIso e X.of).symm.trans r.hom₂)
    let f : X ⟶ Y := ⟨fIso⟩
    refine ⟨f, ?_⟩
    apply Functor.Fiber.hom_ext
    change Hom.mk (RawHom.ofCorePair ((𝟙 B), f)) = φ.1
    rw [← Hom.mk_representative φ.1]
    symm
    apply Quotient.sound
    refine ⟨e, ?_, ?_⟩
    · change (stabilizerIso e B.of).trans
        ((isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl B.of)) =
          r.hom₁
      simpa using he
    · change (stabilizerIso e X.of).trans
        ((isoZeroBiprod (isZero_zero C)).symm.trans fIso) = r.hom₂
      dsimp only [fIso]
      simp

/-- Every object in the strict translation fiber is represented by its
second coordinate in the core. -/
noncomputable instance coreToTranslationFiber_essSurj (B : Core C) :
    (coreToTranslationFiber B).EssSurj where
  mem_essImage A := by
    rcases A with ⟨⟨A₁, A₂⟩, hA⟩
    have hfst : A₁ = B.of := congrArg Translation.of hA
    subst A₁
    exact ⟨⟨A₂⟩, ⟨Iso.refl _⟩⟩

/-- The core-to-fiber functor is an equivalence of categories. -/
noncomputable instance coreToTranslationFiber_isEquivalence (B : Core C) :
    (coreToTranslationFiber B).IsEquivalence where

/-- The strict fiber of the additive translation projection over `B` is
equivalent to `Core(C)`. -/
noncomputable def coreTranslationFiberEquivalence (B : Core C) :
    Core C ≌ TranslationFiber B :=
  (coreToTranslationFiber B).asEquivalence

end SInverseS
end CategoryTheory

end
