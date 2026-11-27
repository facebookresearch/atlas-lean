/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanFlagEndpointTransport
public import MathlibExt.CategoryTheory.Waldhausen.Exact
import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShell

/-!
# Tests for endpoint transport of flagged Quillen spans

These tests exercise raw-span and all material flag formulas, all four
transported exact sequences, reflexive/successive/inverse coherence, the C1B
fixed-endpoint adapter, mixed universes, and flags extracted from degree-two
edgewise Stage shells.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagEndpointTransportTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section SpanApi

variable {X X' X'' Y Y' Y'' : C}
variable (S : QuillenSpan X Y)
variable (eX : X ≅ X') (eY : Y ≅ Y')
  (fX : X' ≅ X'') (fY : Y' ≅ Y'')

example : (QuillenSpan.endpointTransport S eX eY).apex = S.apex := by
  simp

example : (QuillenSpan.endpointTransport S eX eY).l = S.l ≫ eX.hom := by
  simp

example : (QuillenSpan.endpointTransport S eX eY).r = S.r ≫ eY.hom := by
  simp

example : IsAdmissibleEpi (QuillenSpan.endpointTransport S eX eY).l :=
  QuillenSpan.endpointTransport_wl S eX eY

example : IsAdmissibleMono (QuillenSpan.endpointTransport S eX eY).r :=
  QuillenSpan.endpointTransport_wr S eX eY

example :
    QuillenSpan.endpointTransport S (Iso.refl X) (Iso.refl Y) ≅ S :=
  QuillenSpan.endpointTransportReflIso S

example :
    QuillenSpan.endpointTransport S (eX.trans fX) (eY.trans fY) ≅
      QuillenSpan.endpointTransport
        (QuillenSpan.endpointTransport S eX eY) fX fY :=
  QuillenSpan.endpointTransportTransIso S eX eY fX fY

example :
    QuillenSpan.endpointTransport
        (QuillenSpan.endpointTransport S eX eY) eX.symm eY.symm ≅ S :=
  QuillenSpan.endpointTransportSymmIso S eX eY

example :
    (QuillenSpan.endpointTransportTransIso S eX eY fX fY).hom.hom =
      𝟙 S.apex :=
  rfl

example :
    (QuillenSpan.endpointTransportSymmIso S eX eY).inv.hom =
      𝟙 S.apex :=
  rfl

end SpanApi

section FlagFields

variable {X X' Y Y' : C} {S : QuillenSpan X Y}
variable (eX : X ≅ X') (eY : Y ≅ Y')
variable (A : QuillenSpanFlagData S)

example : (A.endpointTransport eX eY).kernelObj = A.kernelObj := by simp

example : (A.endpointTransport eX eY).pushoutObj = A.pushoutObj := by simp

example : (A.endpointTransport eX eY).quotientObj = A.quotientObj := by simp

example : (A.endpointTransport eX eY).kernelι = A.kernelι := by simp

example :
    (A.endpointTransport eX eY).quotientπ = eY.inv ≫ A.quotientπ := by
  simp

example :
    (A.endpointTransport eX eY).sourceToPushout =
      eX.inv ≫ A.sourceToPushout := by
  simp

example :
    (A.endpointTransport eX eY).targetToPushout =
      eY.inv ≫ A.targetToPushout := by
  simp

example :
    (A.endpointTransport eX eY).pushoutToQuotient =
      A.pushoutToQuotient := by
  simp

example :
    IsPushout
      (QuillenSpan.endpointTransport S eX eY).l
      (QuillenSpan.endpointTransport S eX eY).r
      (A.endpointTransport eX eY).sourceToPushout
      (A.endpointTransport eX eY).targetToPushout :=
  (A.endpointTransport eX eY).pushoutSquare

example :
    IsAdmissibleExact
      (ShortComplex.mk
        (A.endpointTransport eX eY).kernelι
        (QuillenSpan.endpointTransport S eX eY).l
        (A.endpointTransport eX eY).kernel_left_zero) :=
  (A.endpointTransport eX eY).kernel_apex_source_exact

example :
    IsAdmissibleExact
      (ShortComplex.mk
        (QuillenSpan.endpointTransport S eX eY).r
        (A.endpointTransport eX eY).quotientπ
        (A.endpointTransport eX eY).right_quotient_zero) :=
  (A.endpointTransport eX eY).apex_target_quotient_exact

example :
    IsAdmissibleExact
      (ShortComplex.mk
        ((A.endpointTransport eX eY).kernelι ≫
          (QuillenSpan.endpointTransport S eX eY).r)
        (A.endpointTransport eX eY).targetToPushout
        (A.endpointTransport eX eY).kernel_targetToPushout_zero) :=
  (A.endpointTransport eX eY).kernel_target_pushout_exact

example :
    IsAdmissibleExact
      (ShortComplex.mk
        (A.endpointTransport eX eY).sourceToPushout
        (A.endpointTransport eX eY).pushoutToQuotient
        (A.endpointTransport eX eY).source_pushoutToQuotient_zero) :=
  (A.endpointTransport eX eY).source_pushout_quotient_exact

end FlagFields

section Coherence

variable {X X' X'' Y Y' Y'' : C} {S : QuillenSpan X Y}
variable (eX : X ≅ X') (eY : Y ≅ Y')
  (fX : X' ≅ X'') (fY : Y' ≅ Y'')
variable (A : QuillenSpanFlagData S)

example :
    QuillenSpanFlagData.transport (QuillenSpan.endpointTransportReflIso S)
        (A.endpointTransport (Iso.refl X) (Iso.refl Y)) = A :=
  A.endpointTransport_refl

example :
    QuillenSpanFlagData.transport
        (QuillenSpan.endpointTransportTransIso S eX eY fX fY)
        (A.endpointTransport (eX.trans fX) (eY.trans fY)) =
      (A.endpointTransport eX eY).endpointTransport fX fY :=
  A.endpointTransport_trans eX eY fX fY

example :
    QuillenSpanFlagData.transport
        (QuillenSpan.endpointTransportSymmIso S eX eY)
        ((A.endpointTransport eX eY).endpointTransport eX.symm eY.symm) =
      A :=
  A.endpointTransport_symm eX eY

end Coherence

section C1BAdapter

variable {X X' Y Y' : C}
variable {S : QuillenSpan X Y} {T : QuillenSpan X' Y'}
variable {eX : X ≅ X'} {eY : Y ≅ Y'}
variable (e : QuillenSpan.EndpointIso S T eX eY)
variable (A : QuillenSpanFlagData S) (B : QuillenSpanFlagData T)

example : QuillenSpan.endpointTransport S eX eY ≅ T :=
  e.endpointTransportIso

example : Span.SpanBicat.apexIso e.endpointTransportIso = e.1 := by
  simp

example : e.endpointTransportIso.hom.hom = e.1.hom := by
  simp

example : e.endpointTransportIso.inv.hom = e.1.inv := by
  simp

example :
    QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY) ⟶ B :=
  QuillenSpanFlagHom.endpointCanonical e A B

example :
    (QuillenSpanFlagHom.endpointCanonical e A B).kernelHom ≫ B.kernelι =
      (QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY)).kernelι :=
  (QuillenSpanFlagHom.endpointCanonical e A B).kernelHom_kernelι

example :
    (QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY)).sourceToPushout ≫
          (QuillenSpanFlagHom.endpointCanonical e A B).pushoutHom =
      B.sourceToPushout :=
  (QuillenSpanFlagHom.endpointCanonical e A B).sourceToPushout_naturality

example :
    (QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY)).targetToPushout ≫
          (QuillenSpanFlagHom.endpointCanonical e A B).pushoutHom =
      B.targetToPushout :=
  (QuillenSpanFlagHom.endpointCanonical e A B).targetToPushout_naturality

example :
    (QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY)).quotientπ ≫
          (QuillenSpanFlagHom.endpointCanonical e A B).quotientHom =
      B.quotientπ :=
  (QuillenSpanFlagHom.endpointCanonical e A B).quotientπ_quotientHom

example :
    (QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY)).pushoutToQuotient ≫
          (QuillenSpanFlagHom.endpointCanonical e A B).quotientHom =
      (QuillenSpanFlagHom.endpointCanonical e A B).pushoutHom ≫
        B.pushoutToQuotient :=
  (QuillenSpanFlagHom.endpointCanonical e A B).pushoutToQuotient_naturality

end C1BAdapter

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example {X X' Y Y' : C₀} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData (QuillenSpan.endpointTransport S eX eY) :=
  A.endpointTransport eX eY

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example {X X' Y Y' : C₁} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData (QuillenSpan.endpointTransport S eX eY) :=
  A.endpointTransport eX eY

end TypeOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example {X X' Y Y' : C₀₁} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData (QuillenSpan.endpointTransport S eX eY) :=
  A.endpointTransport eX eY

example {X X' Y Y' : C₁₀} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData (QuillenSpan.endpointTransport S eX eY) :=
  A.endpointTransport eX eY

end MixedUniverses

section DegreeTwoShell

local instance degreeTwoShellWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example (A : Stage C 5) (k l : Fin 3) (hkl : k ≤ l)
    {X' Y' : C}
    (eX : (edgewiseStageShellPacketNat (n := 2) A k l hkl).source ≅ X')
    (eY : (edgewiseStageShellPacketNat (n := 2) A k l hkl).target ≅ Y') :
    QuillenSpanFlagData
      (QuillenSpan.endpointTransport
        (edgewiseStageShellPacketNat (n := 2) A k l hkl).span eX eY) :=
  (edgewiseStageShellPacketNat (n := 2) A k l hkl).flag.endpointTransport
    eX eY

example (A : Stage C 5) (k l : Fin 3) (hkl : k ≤ l)
    {X' Y' : C}
    (eX : (edgewiseStageShellPacketNat (n := 2) A k l hkl).source ≅ X')
    (eY : (edgewiseStageShellPacketNat (n := 2) A k l hkl).target ≅ Y') :
    ((edgewiseStageShellPacketNat (n := 2) A k l hkl).flag.endpointTransport
      eX eY).kernelObj =
        (edgewiseStageShellPacketNat (n := 2) A k l hkl).flag.kernelObj := by
  simp

end DegreeTwoShell

#print axioms AlgebraicKTheory.QuillenSpanFlagData.endpointTransport
#print axioms AlgebraicKTheory.QuillenSpanFlagData.endpointTransport_trans
#print axioms AlgebraicKTheory.QuillenSpanFlagHom.endpointCanonical

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagEndpointTransportTests

end
