/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.BiproductFunctor
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiber
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationLift
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedPushforward

/-!
# Fiber pushforward for the additive translation projection

Under the equivalence between a strict fiber of the additive `S⁻¹S`
translation projection and `Core C`, pushforward along a base arrow is
residual left translation by the stabilizer of its selected representative.

This file first constructs the literal core translation and the canonical
objectwise comparison between the chosen cocartesian pushforward and the
explicit translation lift.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Left translation by `s` on the core, sending `X` to `s ⊞ X`. -/
noncomputable def coreLeftTranslationFunctor (s : C) :
    Core C ⥤ Core C :=
  (((Functor.const C).obj s).prod' (𝟭 C) ⋙
    biprodFunctor C).core

omit [HasZeroObject C] in
@[simp]
theorem coreLeftTranslationFunctor_obj_of (s : C) (X : Core C) :
    ((coreLeftTranslationFunctor s).obj X).of = (s ⊞ X.of : C) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem coreLeftTranslationFunctor_map_iso_hom
    (s : C) {X Y : Core C} (g : X ⟶ Y) :
    ((coreLeftTranslationFunctor s).map g).iso.hom =
      biprod.map (𝟙 s) g.iso.hom :=
  rfl

/-- The chosen pushforward between strict translation fibers, precomposed
with the canonical equivalence source functor from the core. -/
noncomputable def chosenCoreFiberPushforwardFunctor
    {B T : Translation C} (f : B ⟶ T) :
    Core C ⥤ TranslationFiber (⟨T.of⟩ : Core C) :=
  coreToTranslationFiber (⟨B.of⟩ : Core C) ⋙
    Functor.IsCofibered.fiberPushforwardFunctor
      (p := translationProjection (C := C)) f

@[simp]
theorem chosenCoreFiberPushforwardFunctor_map_val
    {B T : Translation C} (f : B ⟶ T)
    {X Y : Core C} (g : X ⟶ Y) :
    ((chosenCoreFiberPushforwardFunctor f).map g).1 =
      Functor.IsCofibered.fiberPushforwardMap f
        ((coreToTranslationFiber (⟨B.of⟩ : Core C)).map g) :=
  rfl

/-- Explicit core translation by the stabilizer of the selected base-arrow
representative, regarded in the target strict fiber. -/
noncomputable def explicitCoreFiberPushforwardFunctor
    {B T : Translation C} (f : B ⟶ T) :
    Core C ⥤ TranslationFiber (⟨T.of⟩ : Core C) :=
  coreLeftTranslationFunctor (Translation.representative f).stabilizer ⋙
    coreToTranslationFiber (⟨T.of⟩ : Core C)

@[simp]
theorem explicitCoreFiberPushforwardFunctor_obj_val
    {B T : Translation C} (f : B ⟶ T) (X : Core C) :
    ((explicitCoreFiberPushforwardFunctor f).obj X).1 =
      translationLiftObj
        ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f :=
  rfl

/-- Raw zero-stabilized arrow underlying a core morphism in a fixed strict
translation fiber. -/
noncomputable def coreTranslationFiberRawMap
    (B : Core C) {X Y : Core C} (g : X ⟶ Y) :
    RawHom (⟨B.of, X.of⟩ : Pair C) ⟨B.of, Y.of⟩ :=
  by
    change RawHom (Pair.ofCorePair (B, X)) (Pair.ofCorePair (B, Y))
    exact RawHom.ofCorePair ((𝟙 B, g) : (B, X) ⟶ (B, Y))

@[simp]
theorem coreToTranslationFiber_map_val
    (B : Core C) {X Y : Core C} (g : X ⟶ Y) :
    ((coreToTranslationFiber B).map g).1 =
      Hom.mk (coreTranslationFiberRawMap B g) :=
  by
    change (coreFiberPair B).map g =
      Hom.mk (coreTranslationFiberRawMap B g)
    rfl

/-- Raw zero-stabilized arrow underlying explicit core pushforward on a
core isomorphism. -/
noncomputable def explicitCoreFiberPushforwardRawMap
    {B T : Translation C} (f : B ⟶ T)
    {X Y : Core C} (g : X ⟶ Y) :
    RawHom
      (translationLiftObj
        ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f)
      (translationLiftObj
        ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj Y).1 f) :=
  { stabilizer := 0
    hom₁ := (isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl T.of)
    hom₂ := (isoZeroBiprod (isZero_zero C)).symm.trans
      (biprod.mapIso (Iso.refl
        (Translation.representative f).stabilizer) g.iso) }

@[simp]
theorem explicitCoreFiberPushforwardFunctor_map_val
    {B T : Translation C} (f : B ⟶ T)
    {X Y : Core C} (g : X ⟶ Y) :
    ((explicitCoreFiberPushforwardFunctor f).map g).1 =
      Hom.mk (explicitCoreFiberPushforwardRawMap f g) :=
  rfl

/-- Raw arrow obtained by applying the selected stabilizer to a core
isomorphism. -/
noncomputable def translatedCoreRawMap
    {B T : Translation C} (f : B ⟶ T)
    {X Y : Core C} (g : X ⟶ Y) :
    RawHom (⟨B.of, X.of⟩ : Pair C)
      ⟨T.of, (Translation.representative f).stabilizer ⊞ Y.of⟩ where
  stabilizer := (Translation.representative f).stabilizer
  hom₁ := (Translation.representative f).hom
  hom₂ := biprod.mapIso
    (Iso.refl (Translation.representative f).stabilizer) g.iso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit translation lift is natural in the core object. -/
theorem coreFiberTranslationLift_naturality
    {B T : Translation C} (f : B ⟶ T)
    {X Y : Core C} (g : X ⟶ Y) :
    ((coreToTranslationFiber (⟨B.of⟩ : Core C)).map g).1 ≫
        translationLiftHom
          ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj Y).1 f =
      translationLiftHom
          ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f ≫
        ((explicitCoreFiberPushforwardFunctor f).map g).1 := by
  rcases B with ⟨B⟩
  rcases T with ⟨T⟩
  rw [coreToTranslationFiber_map_val,
    explicitCoreFiberPushforwardFunctor_map_val]
  change Hom.comp
      (Hom.mk (coreTranslationFiberRawMap
        (⟨B⟩ : Core C) g))
      (Hom.mk (translationLiftRawHom
        (⟨B, Y.of⟩ : Pair C) f)) =
    Hom.comp
      (Hom.mk (translationLiftRawHom
        (⟨B, X.of⟩ : Pair C) f))
      (Hom.mk (explicitCoreFiberPushforwardRawMap f g))
  rw [Hom.comp_mk, Hom.comp_mk]
  apply Quotient.sound
  let m := translatedCoreRawMap f g
  have hLeft :
      ((coreTranslationFiberRawMap (⟨B⟩ : Core C) g).comp
        (translationLiftRawHom (⟨B, Y.of⟩ : Pair C) f)).Rel m := by
    refine ⟨(isoBiprodZero (isZero_zero C)).symm, ?_, ?_⟩
    · apply Iso.ext
      dsimp [m, translatedCoreRawMap, coreTranslationFiberRawMap,
        RawHom.comp, RawHom.ofCorePair, translationLiftRawHom,
        stabilizerIso]
      change
        biprod.map (isoBiprodZero (isZero_zero C)).symm.hom
              (𝟙 B) ≫ (Translation.representative f).hom.hom =
          (biprod.associator
              (Translation.representative f).stabilizer (0 : C) B).hom ≫
            biprod.map (𝟙 (Translation.representative f).stabilizer)
              ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ 𝟙 B) ≫
                (Translation.representative f).hom.hom
      simpa only [Category.assoc, Category.comp_id] using congrArg
        (fun k => k ≫ (Translation.representative f).hom.hom)
        (rawId_comp_hom
          (Translation.representative f).stabilizer B)
    · apply Iso.ext
      dsimp [m, translatedCoreRawMap, coreTranslationFiberRawMap,
        RawHom.comp, RawHom.ofCorePair, translationLiftRawHom,
        stabilizerIso]
      simp only [biprod.mapIso_hom, Iso.trans_hom, Iso.refl_hom,
        Category.comp_id]
      change
        biprod.map (isoBiprodZero (isZero_zero C)).symm.hom
              (𝟙 X.of) ≫
            biprod.map (𝟙 (Translation.representative f).stabilizer)
              g.iso.hom =
          (biprod.associator
              (Translation.representative f).stabilizer
              (0 : C) X.of).hom ≫
            biprod.map (𝟙 (Translation.representative f).stabilizer)
              ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ g.iso.hom)
      rw [rawId_comp_hom]
      simp only [Category.assoc]
      apply biprod.hom_ext <;> simp [Category.assoc]
  have hRight :
      ((translationLiftRawHom (⟨B, X.of⟩ : Pair C) f).comp
        (explicitCoreFiberPushforwardRawMap f g)).Rel m := by
    refine ⟨(isoZeroBiprod (isZero_zero C)).symm, ?_, ?_⟩
    · apply Iso.ext
      dsimp [m, translatedCoreRawMap,
        explicitCoreFiberPushforwardRawMap, RawHom.comp,
        translationLiftRawHom, stabilizerIso]
      change
        biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom
              (𝟙 B) ≫ (Translation.representative f).hom.hom =
          (biprod.associator (0 : C)
              (Translation.representative f).stabilizer B).hom ≫
            biprod.map (𝟙 (0 : C))
              (Translation.representative f).hom.hom ≫
                (isoZeroBiprod (isZero_zero C)).symm.hom ≫ 𝟙 T
      simpa only [Category.assoc, Category.comp_id] using
        rawComp_id_hom (Translation.representative f).hom.hom
    · apply Iso.ext
      dsimp [m, translatedCoreRawMap,
        explicitCoreFiberPushforwardRawMap, RawHom.comp,
        translationLiftRawHom, stabilizerIso]
      change
        biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom
              (𝟙 X.of) ≫
            biprod.map (𝟙 (Translation.representative f).stabilizer)
              g.iso.hom =
          (biprod.associator (0 : C)
              (Translation.representative f).stabilizer X.of).hom ≫
            biprod.map (𝟙 (0 : C))
              (𝟙 ((Translation.representative f).stabilizer ⊞ X.of)) ≫
                (isoZeroBiprod (isZero_zero C)).symm.hom ≫
                  biprod.map
                    (𝟙 (Translation.representative f).stabilizer) g.iso.hom
      apply biprod.hom_ext <;> simp [Category.assoc]
  exact hLeft.trans hRight.symm

/-- Canonical comparison between the chosen cocartesian pushforward target
and the explicit target obtained by adding the selected stabilizer. -/
noncomputable def chosenExplicitCoreFiberPushforwardIsoApp
    {B T : Translation C} (f : B ⟶ T) (X : Core C) :
    (chosenCoreFiberPushforwardFunctor f).obj X ≅
      (explicitCoreFiberPushforwardFunctor f).obj X := by
  let p := translationProjection (C := C)
  let a := (coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X
  let _ : p.IsStronglyCocartesian f (translationLiftHom a.1 f) := by
    dsimp only [p]
    exact translationLiftHom_isStronglyCocartesian a.1 f
  let e := Functor.IsCocartesian.codomainUniqueUpToIso p f
    (Functor.IsCofibered.pushforwardMap a.2 f)
    (translationLiftHom a.1 f)
  have he : p.IsHomLift (𝟙 T) e.hom := by
    dsimp only [e]
    exact Functor.IsCocartesian.map_isHomLift p f
      (Functor.IsCofibered.pushforwardMap a.2 f)
      (translationLiftHom a.1 f)
  exact Functor.IsCofibered.fiberIsoOfTotalIso e he

/-- The chosen lift followed by the comparison is the explicit translation
lift. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_chosenExplicitCoreFiberPushforwardIsoApp_hom
    {B T : Translation C} (f : B ⟶ T) (X : Core C) :
    Functor.IsCofibered.pushforwardMap
          ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).2 f ≫
        (chosenExplicitCoreFiberPushforwardIsoApp f X).hom.1 =
      translationLiftHom
        ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f := by
  let _ : (translationProjection (C := C)).IsStronglyCocartesian f
      (translationLiftHom
        ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f) :=
    translationLiftHom_isStronglyCocartesian
      (C := C)
      ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f
  exact Functor.IsCocartesian.fac
    (translationProjection (C := C)) f
    (Functor.IsCofibered.pushforwardMap
      ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).2 f)
    (translationLiftHom
      ((coreToTranslationFiber (⟨B.of⟩ : Core C)).obj X).1 f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The objectwise chosen/explicit pushforward comparison is natural in the
core object. -/
theorem chosenExplicitCoreFiberPushforwardIsoApp_naturality
    {B T : Translation C} (f : B ⟶ T)
    {X Y : Core C} (g : X ⟶ Y) :
    (chosenCoreFiberPushforwardFunctor f).map g ≫
        (chosenExplicitCoreFiberPushforwardIsoApp f Y).hom =
      (chosenExplicitCoreFiberPushforwardIsoApp f X).hom ≫
        (explicitCoreFiberPushforwardFunctor f).map g := by
  rcases B with ⟨B⟩
  rcases T with ⟨T⟩
  let p := translationProjection (C := C)
  let aX := (coreToTranslationFiber (⟨B⟩ : Core C)).obj X
  let aY := (coreToTranslationFiber (⟨B⟩ : Core C)).obj Y
  let liftX := Functor.IsCofibered.pushforwardMap aX.2 f
  let left := (chosenCoreFiberPushforwardFunctor f).map g ≫
    (chosenExplicitCoreFiberPushforwardIsoApp f Y).hom
  let right := (chosenExplicitCoreFiberPushforwardIsoApp f X).hom ≫
    (explicitCoreFiberPushforwardFunctor f).map g
  apply Functor.Fiber.hom_ext
  change left.1 = right.1
  let _ : p.IsStronglyCocartesian f liftX := by
    dsimp only [p, liftX]
    exact Functor.IsCofibered.pushforwardMap_isStronglyCocartesian
      (p := translationProjection (C := C))
      (ha := aX.2) (f := f)
  let _ : p.IsHomLift (𝟙 (⟨T⟩ : Translation C)) left.1 := left.2
  let _ : p.IsHomLift (𝟙 (⟨T⟩ : Translation C)) right.1 := right.2
  apply Functor.IsCocartesian.ext p f liftX left.1 right.1
  change
    Functor.IsCofibered.pushforwardMap aX.2 f ≫
        (((chosenCoreFiberPushforwardFunctor f).map g).1 ≫
          (chosenExplicitCoreFiberPushforwardIsoApp f Y).hom.1) =
      Functor.IsCofibered.pushforwardMap aX.2 f ≫
        ((chosenExplicitCoreFiberPushforwardIsoApp f X).hom.1 ≫
          ((explicitCoreFiberPushforwardFunctor f).map g).1)
  calc
    _ = (Functor.IsCofibered.pushforwardMap aX.2 f ≫
          Functor.IsCofibered.fiberPushforwardMap f
            ((coreToTranslationFiber (⟨B⟩ : Core C)).map g)) ≫
        (chosenExplicitCoreFiberPushforwardIsoApp f Y).hom.1 := by
      rw [chosenCoreFiberPushforwardFunctor_map_val]
      exact (Category.assoc _ _ _).symm
    _ = (((coreToTranslationFiber (⟨B⟩ : Core C)).map g).1 ≫
          Functor.IsCofibered.pushforwardMap aY.2 f) ≫
        (chosenExplicitCoreFiberPushforwardIsoApp f Y).hom.1 := by
      rw [Functor.IsCofibered.pushforwardMap_comp_fiberPushforwardMap]
    _ = ((coreToTranslationFiber (⟨B⟩ : Core C)).map g).1 ≫
        (Functor.IsCofibered.pushforwardMap aY.2 f ≫
          (chosenExplicitCoreFiberPushforwardIsoApp f Y).hom.1) :=
      Category.assoc _ _ _
    _ = ((coreToTranslationFiber (⟨B⟩ : Core C)).map g).1 ≫
        translationLiftHom aY.1 f := by
      rw [pushforwardMap_comp_chosenExplicitCoreFiberPushforwardIsoApp_hom]
    _ = translationLiftHom aX.1 f ≫
        ((explicitCoreFiberPushforwardFunctor f).map g).1 :=
      coreFiberTranslationLift_naturality f g
    _ = (Functor.IsCofibered.pushforwardMap aX.2 f ≫
          (chosenExplicitCoreFiberPushforwardIsoApp f X).hom.1) ≫
        ((explicitCoreFiberPushforwardFunctor f).map g).1 := by
      rw [pushforwardMap_comp_chosenExplicitCoreFiberPushforwardIsoApp_hom]
    _ = _ := Category.assoc _ _ _

/-- Under the strict-fiber/core equivalences, chosen pushforward along a
translation arrow is naturally isomorphic to left translation by the
stabilizer of its selected representative. -/
noncomputable def chosenExplicitCoreFiberPushforwardIso
    {B T : Translation C} (f : B ⟶ T) :
    chosenCoreFiberPushforwardFunctor f ≅
      explicitCoreFiberPushforwardFunctor f :=
  NatIso.ofComponents
    (chosenExplicitCoreFiberPushforwardIsoApp f)
    (fun g => chosenExplicitCoreFiberPushforwardIsoApp_naturality f g)

end SInverseS
end CategoryTheory

end
