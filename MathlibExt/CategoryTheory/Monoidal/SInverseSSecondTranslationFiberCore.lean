/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiber

/-!
# Raw fiberwise second/core translation comparison

Second-coordinate translation of the canonical zero-stabilized fiber arrow
is related to the explicit zero-stabilized arrow obtained by applying
`id_A ⊞ g` in the second coordinate.  This is the raw quotient-coherence
calculation needed to identify fiberwise second translation with core left
translation.

The endpoint transport from this explicit representative to
`coreLeftTranslationFunctor` is deliberately deferred.  This file makes no
functor-isomorphism, comma-to-fiber, homology, localization,
spectral-sequence, realization, or CGWH claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Explicit canonical zero-stabilized arrow in a strict translation
fiber, with endpoints kept definitionally transparent. -/
noncomputable def explicitCoreFiberRawMap
    (B : C) {X Y : Core C} (g : X ⟶ Y) :
    RawHom ⟨B, X.of⟩ ⟨B, Y.of⟩ where
  stabilizer := 0
  hom₁ := (isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl B)
  hom₂ := (isoZeroBiprod (isZero_zero C)).symm.trans g.iso

/-- Explicit zero-stabilized arrow obtained by translating a core
isomorphism in the second coordinate. -/
noncomputable def explicitCoreSecondTranslationRawMap
    (A B : C) {X Y : Core C} (g : X ⟶ Y) :
    RawHom (translateSecondObj A ⟨B, X.of⟩)
      (translateSecondObj A ⟨B, Y.of⟩) where
  stabilizer := 0
  hom₁ := (isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl B)
  hom₂ := (isoZeroBiprod (isZero_zero C)).symm.trans
    (biprod.mapIso (Iso.refl A) g.iso)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translating the canonical fiber arrow in the second coordinate is
related to the explicit core-translation representative. -/
theorem translateSecond_coreTranslationFiberRawMap_rel
    (A : C) (B : Core C) {X Y : Core C} (g : X ⟶ Y) :
    (explicitCoreFiberRawMap B.of g).translateSecond A |>.Rel
      (explicitCoreSecondTranslationRawMap A B.of g) := by
  dsimp only [explicitCoreFiberRawMap,
    explicitCoreSecondTranslationRawMap, RawHom.translateSecond]
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · apply Iso.ext
    rw [stabilizerIso_refl, Iso.refl_trans]
  · apply Iso.ext
    rw [stabilizerIso_refl, Iso.refl_trans]
    change
      (isoZeroBiprod (isZero_zero C)).symm.hom ≫
          biprod.map (𝟙 A) g.iso.hom =
        (swapStabilizerIso A (0 : C) X.of).hom ≫
          biprod.map (𝟙 A)
            ((isoZeroBiprod (isZero_zero C)).symm.hom ≫ g.iso.hom)
    apply biprod.hom_ext'
    · exact (isZero_zero C).eq_of_src _ _
    · apply biprod.hom_ext' <;>
        simp [Category.assoc]

end SInverseS
end CategoryTheory

end
