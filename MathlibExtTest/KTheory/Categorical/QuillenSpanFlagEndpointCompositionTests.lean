/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanFlagEndpointComposition

/-!
# Tests for endpoint-compatible flagged-span composition

These tests exercise ordered binary raw-span composition, all four pullback
projection formulas, flag material maps, identity/symmetry/transitivity,
associator-conjugated three-step coherence, mixed universes, and the degree-two
`01`, `12`, then `02` long-shell specialization.
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

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagEndpointCompositionTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section Binary

variable {X0 X1 X2 Y0 Y1 Y2 : C}
variable {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
  {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
variable {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
variable (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
  (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2)

example : QuillenSpan.EndpointIso
    (Span.comp S01 S12) (Span.comp T01 T12) e0 e2 :=
  c01.comp c12

example :
    (c01.comp c12).1.hom ≫ pullback.fst T01.r T12.l =
      pullback.fst S01.r S12.l ≫ c01.1.hom :=
  c01.comp_hom_fst c12

example :
    (c01.comp c12).1.hom ≫ pullback.snd T01.r T12.l =
      pullback.snd S01.r S12.l ≫ c12.1.hom :=
  c01.comp_hom_snd c12

example :
    (c01.comp c12).1.inv ≫ pullback.fst S01.r S12.l =
      pullback.fst T01.r T12.l ≫ c01.1.inv :=
  c01.comp_inv_fst c12

example :
    (c01.comp c12).1.inv ≫ pullback.snd S01.r S12.l =
      pullback.snd T01.r T12.l ≫ c12.1.inv :=
  c01.comp_inv_snd c12

example :
    (QuillenSpan.EndpointIso.refl S01).comp
        (QuillenSpan.EndpointIso.refl S12) =
      QuillenSpan.EndpointIso.refl (Span.comp S01 S12) :=
  QuillenSpan.EndpointIso.comp_refl

example : (c01.comp c12).symm = c01.symm.comp c12.symm :=
  c01.comp_symm c12

variable {Z0 Z1 Z2 : C} {U01 : QuillenSpan Z0 Z1}
  {U12 : QuillenSpan Z1 Z2}
variable {f0 : Y0 ≅ Z0} {f1 : Y1 ≅ Z1} {f2 : Y2 ≅ Z2}
variable (d01 : QuillenSpan.EndpointIso T01 U01 f0 f1)
  (d12 : QuillenSpan.EndpointIso T12 U12 f1 f2)

example :
    (c01.trans d01).comp (c12.trans d12) =
      (c01.comp c12).trans (d01.comp d12) :=
  QuillenSpan.EndpointIso.comp_trans c01 c12 d01 d12

end Binary

section FlagBinary

variable {X0 X1 X2 Y0 Y1 Y2 : C}
variable {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
  {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
variable {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
variable (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
  (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2)
variable (A : QuillenSpanFlagData (Span.comp S01 S12))
  (B : QuillenSpanFlagData (Span.comp T01 T12))

example :
    QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2) ⟶ B :=
  QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B

example :
    (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).kernelHom ≫
        B.kernelι =
      (QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2)).kernelι :=
  (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).kernelHom_kernelι

example :
    (QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2)).sourceToPushout ≫
          (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).pushoutHom =
      B.sourceToPushout :=
  (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).sourceToPushout_naturality

example :
    (QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2)).targetToPushout ≫
          (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).pushoutHom =
      B.targetToPushout :=
  (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).targetToPushout_naturality

example :
    (QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2)).quotientπ ≫
          (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).quotientHom =
      B.quotientπ :=
  (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).quotientπ_quotientHom

example :
    (QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2)).pushoutToQuotient ≫
          (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).quotientHom =
      (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).pushoutHom ≫
        B.pushoutToQuotient :=
  (QuillenSpanFlagHom.endpointCompCanonical c01 c12 A B).pushoutToQuotient_naturality

end FlagBinary

section TransportInterchange

variable {X X' Y Y' : C} {S T : QuillenSpan X Y}
variable (i : S ≅ T) (eX : X ≅ X') (eY : Y ≅ Y')
variable (A : QuillenSpanFlagData S)

example :
    (QuillenSpanFlagData.transport i A).endpointTransport eX eY =
      QuillenSpanFlagData.transport
        (QuillenSpan.endpointTransportIsoMap i eX eY)
        (A.endpointTransport eX eY) :=
  A.endpointTransport_transport i eX eY

end TransportInterchange

section Associativity

variable {X0 X1 X2 X3 Y0 Y1 Y2 Y3 : C}
variable {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
  {S23 : QuillenSpan X2 X3}
  {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
  {T23 : QuillenSpan Y2 Y3}
variable {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
  {e3 : X3 ≅ Y3}
variable (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
  (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2)
  (c23 : QuillenSpan.EndpointIso S23 T23 e2 e3)

example :
    ((c01.comp c12).comp c23).rebase
        (QuillenSpan.associator S01 S12 S23).symm
        (QuillenSpan.associator T01 T12 T23) =
      c01.comp (c12.comp c23) :=
  QuillenSpan.EndpointIso.comp_assoc c01 c12 c23

end Associativity

section StageShell

local instance stageShellWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

variable {a : SimplexCategory}
variable (A B : Stage C (edgewiseQ.obj a).len)
variable {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
variable {eK : (edgewiseStageShellPacket A k l hkl).source ≅
    (edgewiseStageShellPacket B k l hkl).source}
variable {eL : (edgewiseStageShellPacket A k l hkl).target ≅
    (edgewiseStageShellPacket B k l hkl).target}
variable {eR : (edgewiseStageShellPacket A l r hlr).target ≅
    (edgewiseStageShellPacket B l r hlr).target}
variable
  (cKL : QuillenSpan.EndpointIso
    (edgewiseStageShellPacket A k l hkl).span
    (edgewiseStageShellPacket B k l hkl).span eK eL)
  (cLR : QuillenSpan.EndpointIso
    (edgewiseStageShellPacket A l r hlr).span
    (edgewiseStageShellPacket B l r hlr).span eL eR)

example :
    (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).1.hom ≫
        edgewiseStageShellToLeft B hkl hlr =
      edgewiseStageShellToLeft A hkl hlr ≫ cKL.1.hom :=
  edgewiseStageShellEndpointIsoComp_hom_left A B hkl hlr cKL cLR

example :
    (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).1.hom ≫
        edgewiseStageShellToRight B hkl hlr =
      edgewiseStageShellToRight A hkl hlr ≫ cLR.1.hom :=
  edgewiseStageShellEndpointIsoComp_hom_right A B hkl hlr cKL cLR

example :
    let cLong := edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR
    QuillenSpanFlagData.transport cLong.endpointTransportIso
        ((edgewiseStageShellPacket A k r (hkl.trans hlr)).flag.endpointTransport
          eK eR) ⟶
      (edgewiseStageShellPacket B k r (hkl.trans hlr)).flag :=
  edgewiseStageShellFlagEndpointCompCanonical A B hkl hlr cKL cLR

example :
    let f := edgewiseStageShellFlagEndpointCompCanonical
      A B hkl hlr cKL cLR
    f.kernelHom ≫
        (edgewiseStageShellPacket B k r (hkl.trans hlr)).flag.kernelι =
      (QuillenSpanFlagData.transport
        (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).endpointTransportIso
        ((edgewiseStageShellPacket A k r (hkl.trans hlr)).flag.endpointTransport
          eK eR)).kernelι :=
  (edgewiseStageShellFlagEndpointCompCanonical
    A B hkl hlr cKL cLR).kernelHom_kernelι

example :
    let f := edgewiseStageShellFlagEndpointCompCanonical
      A B hkl hlr cKL cLR
    (QuillenSpanFlagData.transport
      (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).endpointTransportIso
      ((edgewiseStageShellPacket A k r (hkl.trans hlr)).flag.endpointTransport
        eK eR)).sourceToPushout ≫ f.pushoutHom =
      (edgewiseStageShellPacket B k r
        (hkl.trans hlr)).flag.sourceToPushout :=
  (edgewiseStageShellFlagEndpointCompCanonical
    A B hkl hlr cKL cLR).sourceToPushout_naturality

example :
    let f := edgewiseStageShellFlagEndpointCompCanonical
      A B hkl hlr cKL cLR
    (QuillenSpanFlagData.transport
      (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).endpointTransportIso
      ((edgewiseStageShellPacket A k r (hkl.trans hlr)).flag.endpointTransport
        eK eR)).quotientπ ≫ f.quotientHom =
      (edgewiseStageShellPacket B k r (hkl.trans hlr)).flag.quotientπ :=
  (edgewiseStageShellFlagEndpointCompCanonical
    A B hkl hlr cKL cLR).quotientπ_quotientHom

example := edgewiseStageShellFlagEndpointComp_source A B hkl hlr cKL cLR

example := edgewiseStageShellFlagEndpointComp_map A B hkl hlr cKL cLR

end StageShell

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example {X0 X1 X2 Y0 Y1 Y2 : C₀}
    {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
    {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
    {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    QuillenSpan.EndpointIso
      (Span.comp S01 S12) (Span.comp T01 T12) e0 e2 :=
  c01.comp c12

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example {X0 X1 X2 Y0 Y1 Y2 : C₁}
    {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
    {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
    {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    QuillenSpan.EndpointIso
      (Span.comp S01 S12) (Span.comp T01 T12) e0 e2 :=
  c01.comp c12

end TypeOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example {X0 X1 X2 Y0 Y1 Y2 : C₀₁}
    {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
    {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
    {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    QuillenSpan.EndpointIso
      (Span.comp S01 S12) (Span.comp T01 T12) e0 e2 :=
  c01.comp c12

example {X0 X1 X2 Y0 Y1 Y2 : C₁₀}
    {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
    {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
    {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    QuillenSpan.EndpointIso
      (Span.comp S01 S12) (Span.comp T01 T12) e0 e2 :=
  c01.comp c12

end MixedUniverses

section DegreeTwo

local instance degreeTwoWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

theorem degreeTwo_h01 : (0 : Fin 3) ≤ 1 := by decide

theorem degreeTwo_h12 : (1 : Fin 3) ≤ 2 := by decide

private structure DegreeTwoComparison where
  A : Stage C (edgewiseQ.obj ⦋2⦌).len
  B : Stage C (edgewiseQ.obj ⦋2⦌).len
  e0 : (edgewiseStageShellPacket (C := C) A
      (0 : Fin 3) 1 degreeTwo_h01).source ≅
    (edgewiseStageShellPacket (C := C) B
      (0 : Fin 3) 1 degreeTwo_h01).source
  e1 : (edgewiseStageShellPacket (C := C) A
      (0 : Fin 3) 1 degreeTwo_h01).target ≅
    (edgewiseStageShellPacket (C := C) B
      (0 : Fin 3) 1 degreeTwo_h01).target
  e2 : (edgewiseStageShellPacket (C := C) A
      (1 : Fin 3) 2 degreeTwo_h12).target ≅
    (edgewiseStageShellPacket (C := C) B
      (1 : Fin 3) 2 degreeTwo_h12).target
  c01 : QuillenSpan.EndpointIso
    (edgewiseStageShellPacket (C := C) A
      (0 : Fin 3) 1 degreeTwo_h01).span
    (edgewiseStageShellPacket (C := C) B
      (0 : Fin 3) 1 degreeTwo_h01).span e0 e1
  c12 : QuillenSpan.EndpointIso
    (edgewiseStageShellPacket (C := C) A
      (1 : Fin 3) 2 degreeTwo_h12).span
    (edgewiseStageShellPacket (C := C) B
      (1 : Fin 3) 2 degreeTwo_h12).span e1 e2

/-- In degree two, the `02` shell is the ordered composite `01` then `12`. -/
private noncomputable def degreeTwo_longSpanIso
    (D : DegreeTwoComparison (C := C)) :=
  edgewiseStageShellSpanCompIso (C := C) D.A degreeTwo_h01 degreeTwo_h12

private noncomputable def degreeTwo_endpointIso
    (D : DegreeTwoComparison (C := C)) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellPacket (C := C) D.A (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).span
      (edgewiseStageShellPacket (C := C) D.B (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).span D.e0 D.e2 :=
  by
    simpa only using edgewiseStageShellEndpointIsoComp (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12

private theorem degreeTwo_endpointIso_hom_left
    (D : DegreeTwoComparison (C := C)) :
    (edgewiseStageShellEndpointIsoComp (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
        (eK := D.e0) (eL := D.e1) (eR := D.e2)
        D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).1.hom ≫
        edgewiseStageShellToLeft (C := C) D.B degreeTwo_h01 degreeTwo_h12 =
      edgewiseStageShellToLeft (C := C) D.A degreeTwo_h01 degreeTwo_h12 ≫
        D.c01.1.hom :=
  by
    simpa only using edgewiseStageShellEndpointIsoComp_hom_left (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12

private theorem degreeTwo_endpointIso_hom_right
    (D : DegreeTwoComparison (C := C)) :
    (edgewiseStageShellEndpointIsoComp (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
        (eK := D.e0) (eL := D.e1) (eR := D.e2)
        D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).1.hom ≫
        edgewiseStageShellToRight (C := C) D.B degreeTwo_h01 degreeTwo_h12 =
      edgewiseStageShellToRight (C := C) D.A degreeTwo_h01 degreeTwo_h12 ≫
        D.c12.1.hom :=
  by
    simpa only using edgewiseStageShellEndpointIsoComp_hom_right (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12

private noncomputable def degreeTwo_flagHom
    (D : DegreeTwoComparison (C := C)) :
    let cLong := edgewiseStageShellEndpointIsoComp (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12
    QuillenSpanFlagData.transport cLong.endpointTransportIso
        ((edgewiseStageShellPacket (C := C) D.A (0 : Fin 3) 2
          (degreeTwo_h01.trans degreeTwo_h12)).flag.endpointTransport D.e0 D.e2) ⟶
      (edgewiseStageShellPacket (C := C) D.B (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).flag :=
  by
    simpa only using edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12

private theorem degreeTwo_flagHom_kernel
    (D : DegreeTwoComparison (C := C)) :
    let f := edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12
    f.kernelHom ≫
        (edgewiseStageShellPacket (C := C) D.B (0 : Fin 3) 2
          (degreeTwo_h01.trans degreeTwo_h12)).flag.kernelι =
      (QuillenSpanFlagData.transport
        (edgewiseStageShellEndpointIsoComp (C := C)
          (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
          (eK := D.e0) (eL := D.e1) (eR := D.e2)
          D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).endpointTransportIso
        ((edgewiseStageShellPacket (C := C) D.A (0 : Fin 3) 2
          (degreeTwo_h01.trans degreeTwo_h12)).flag.endpointTransport D.e0 D.e2)).kernelι :=
  by
    simpa only using
      (edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).kernelHom_kernelι

private theorem degreeTwo_flagHom_pushout
    (D : DegreeTwoComparison (C := C)) :
    let f := edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12
    (QuillenSpanFlagData.transport
      (edgewiseStageShellEndpointIsoComp (C := C)
        (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
        (eK := D.e0) (eL := D.e1) (eR := D.e2)
        D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).endpointTransportIso
      ((edgewiseStageShellPacket (C := C) D.A (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).flag.endpointTransport D.e0 D.e2)).sourceToPushout ≫
        f.pushoutHom =
      (edgewiseStageShellPacket (C := C) D.B (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).flag.sourceToPushout := by
  simpa only using
    (edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).sourceToPushout_naturality

private theorem degreeTwo_flagHom_quotient
    (D : DegreeTwoComparison (C := C)) :
    let f := edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12
    (QuillenSpanFlagData.transport
      (edgewiseStageShellEndpointIsoComp (C := C)
        (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
        (eK := D.e0) (eL := D.e1) (eR := D.e2)
        D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).endpointTransportIso
      ((edgewiseStageShellPacket (C := C) D.A (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).flag.endpointTransport D.e0 D.e2)).quotientπ ≫
        f.quotientHom =
      (edgewiseStageShellPacket (C := C) D.B (0 : Fin 3) 2
        (degreeTwo_h01.trans degreeTwo_h12)).flag.quotientπ := by
  simpa only using
    (edgewiseStageShellFlagEndpointCompCanonical (C := C)
      (k := (0 : Fin 3)) (l := (1 : Fin 3)) (r := (2 : Fin 3))
      (eK := D.e0) (eL := D.e1) (eR := D.e2)
      D.A D.B degreeTwo_h01 degreeTwo_h12 D.c01 D.c12).quotientπ_quotientHom

end DegreeTwo

#print axioms AlgebraicKTheory.QuillenSpan.EndpointIso.comp
#print axioms AlgebraicKTheory.QuillenSpan.EndpointIso.comp_assoc
#print axioms AlgebraicKTheory.edgewiseStageShellFlagEndpointComp_map

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagEndpointCompositionTests

end
