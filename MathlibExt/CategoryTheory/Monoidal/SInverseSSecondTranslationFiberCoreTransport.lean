/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiberCore
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiberPushforward

/-!
# Transporting fiberwise second translation to core translation

The transparent raw comparison for second-coordinate translation is lifted
through the quotient and the strict-fiber subtype by heterogeneous equality.
This avoids dependent rewriting inside the opaque implementation of
`coreLeftTranslationFunctor`.  Functor extensionality then identifies
fiberwise second translation with core left translation.

No comma-to-fiber, homology, localization, spectral-sequence, realization,
or CGWH claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The object routes through fiberwise second translation and core left
translation agree. -/
theorem coreSecondTranslationFiber_obj_eq (A B X : Core C) :
    (coreToTranslationFiber B ⋙
      secondTranslationFiberFunctor A.of
        (⟨B.of⟩ : Translation C)).obj X =
    (coreLeftTranslationFunctor A.of ⋙
      coreToTranslationFiber B).obj X :=
  rfl

/-- The two map routes are heterogeneously equal; this is the proof-cast
stable form of the transparent raw quotient relation. -/
theorem coreSecondTranslationFiber_map_heq
    (A B : Core C) {X Y : Core C} (g : X ⟶ Y) :
    HEq
      ((coreToTranslationFiber B ⋙
        secondTranslationFiberFunctor A.of
          (⟨B.of⟩ : Translation C)).map g)
      ((coreLeftTranslationFunctor A.of ⋙
        coreToTranslationFiber B).map g) := by
  have hFirst : HEq
      ((coreToTranslationFiber B ⋙
        secondTranslationFiberFunctor A.of
          (⟨B.of⟩ : Translation C)).map g).1
      (Hom.mk ((explicitCoreFiberRawMap B.of g).translateSecond A.of)) := by
    rfl
  have hSecond : HEq
      ((coreLeftTranslationFunctor A.of ⋙
        coreToTranslationFiber B).map g).1
      (Hom.mk (explicitCoreSecondTranslationRawMap A.of B.of g)) := by
    rfl
  have hQuotient :
      Hom.mk ((explicitCoreFiberRawMap B.of g).translateSecond A.of) =
        Hom.mk (explicitCoreSecondTranslationRawMap A.of B.of g) :=
    Quotient.sound
      (translateSecond_coreTranslationFiberRawMap_rel A.of B g)
  have hVal : HEq
      ((coreToTranslationFiber B ⋙
        secondTranslationFiberFunctor A.of
          (⟨B.of⟩ : Translation C)).map g).1
      ((coreLeftTranslationFunctor A.of ⋙
        coreToTranslationFiber B).map g).1 :=
    hFirst.trans ((heq_of_eq hQuotient).trans hSecond.symm)
  apply (Subtype.heq_iff_coe_heq rfl (by rfl)).2
  exact hVal

/-- Fiberwise second translation is equal to core left translation under
the canonical core-to-fiber functor. -/
theorem coreSecondTranslationFiberFunctor_eq (A B : Core C) :
    coreToTranslationFiber B ⋙
        secondTranslationFiberFunctor A.of
          (⟨B.of⟩ : Translation C) =
      coreLeftTranslationFunctor A.of ⋙ coreToTranslationFiber B :=
  Functor.hext (coreSecondTranslationFiber_obj_eq A B)
    (fun _ _ g => coreSecondTranslationFiber_map_heq A B g)

/-- Natural-isomorphism form of the fiberwise second/core translation
comparison. -/
noncomputable def coreSecondTranslationFiberIso (A B : Core C) :
    coreToTranslationFiber B ⋙
        secondTranslationFiberFunctor A.of
          (⟨B.of⟩ : Translation C) ≅
      coreLeftTranslationFunctor A.of ⋙ coreToTranslationFiber B :=
  eqToIso (coreSecondTranslationFiberFunctor_eq A B)

end SInverseS
end CategoryTheory

end
