/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShell

/-!
# Stage shell packet tests

These tests pin the literal six-cell flag, source-first span orientation,
strict edgewise reindexing, long-shell pullback and composition, and repeated
shell identity.  They make no choice of a grid from a quotient class and no
all-degree, realization, additivity, or Q/S claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagStageShellTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenSpanFlagStageShellTestsWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example (B : Stage C 3) : QuillenStageShellData C :=
  QuillenStageShellData.ofStageThree B

/-- A packet carries no independent span or flag choice: it is canonically
recovered from its sole Stage field. -/
example (D : QuillenStageShellData C) :
    D = QuillenStageShellData.ofStageThree D.stage := by
  cases D
  rfl

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).stage = B :=
  QuillenStageShellData.ofStageThree_stage B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).span.apex =
      B.obj.obj (interval (0 : Fin 4) 2 (by decide)) :=
  QuillenStageShellData.ofStageThree_span_apex B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).span.l =
      B.obj.map (vert (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 2 by decide)) :=
  QuillenStageShellData.ofStageThree_span_l B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).span.r =
      B.obj.map (horiz (show (0 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  QuillenStageShellData.ofStageThree_span_r B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.kernelObj =
      B.obj.obj (interval (0 : Fin 4) 1 (by decide)) :=
  QuillenStageShellData.ofStageThree_flag_kernelObj B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.pushoutObj =
      B.obj.obj (interval (1 : Fin 4) 3 (by decide)) :=
  QuillenStageShellData.ofStageThree_flag_pushoutObj B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.quotientObj =
      B.obj.obj (interval (2 : Fin 4) 3 (by decide)) :=
  QuillenStageShellData.ofStageThree_flag_quotientObj B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.kernelι =
      B.obj.map (horiz (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 2 by decide)) :=
  QuillenStageShellData.ofStageThree_flag_kernelι B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.quotientπ =
      B.obj.map (vert (show (0 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  QuillenStageShellData.ofStageThree_flag_quotientπ B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.sourceToPushout =
      B.obj.map (horiz (show (1 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  QuillenStageShellData.ofStageThree_flag_sourceToPushout B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.targetToPushout =
      B.obj.map (vert (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 3 by decide)) :=
  QuillenStageShellData.ofStageThree_flag_targetToPushout B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.pushoutToQuotient =
      B.obj.map (vert (show (1 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  QuillenStageShellData.ofStageThree_flag_pushoutToQuotient B

example (B : Stage C 3) :
    (QuillenStageShellData.ofStageThree B).flag.kernelι ≫
        (QuillenStageShellData.ofStageThree B).span.r =
      B.obj.map (horiz (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 3 by decide)) :=
  QuillenStageShellData.ofStageThree_flag_kernelι_comp_span_r B

example (B : Stage C 3) :
    IsPushout
      (QuillenStageShellData.ofStageThree B).span.l
      (QuillenStageShellData.ofStageThree B).span.r
      (QuillenStageShellData.ofStageThree B).flag.sourceToPushout
      (QuillenStageShellData.ofStageThree B).flag.targetToPushout :=
  (QuillenStageShellData.ofStageThree B).flag.pushoutSquare

example (B : Stage C 3) :
    IsAdmissibleExact
      (ShortComplex.mk
        (QuillenStageShellData.ofStageThree B).flag.kernelι
        (QuillenStageShellData.ofStageThree B).span.l
        (QuillenStageShellData.ofStageThree B).flag.kernel_left_zero) :=
  (QuillenStageShellData.ofStageThree B).flag.kernel_apex_source_exact

example (B : Stage C 3) :
    IsAdmissibleExact
      (ShortComplex.mk
        (QuillenStageShellData.ofStageThree B).span.r
        (QuillenStageShellData.ofStageThree B).flag.quotientπ
        (QuillenStageShellData.ofStageThree B).flag.right_quotient_zero) :=
  (QuillenStageShellData.ofStageThree B).flag.apex_target_quotient_exact

example (B : Stage C 3) :
    IsAdmissibleExact
      (ShortComplex.mk
        ((QuillenStageShellData.ofStageThree B).flag.kernelι ≫
          (QuillenStageShellData.ofStageThree B).span.r)
        (QuillenStageShellData.ofStageThree B).flag.targetToPushout
        (QuillenStageShellData.ofStageThree B).flag.kernel_targetToPushout_zero) :=
  (QuillenStageShellData.ofStageThree B).flag.kernel_target_pushout_exact

example (B : Stage C 3) :
    IsAdmissibleExact
      (ShortComplex.mk
        (QuillenStageShellData.ofStageThree B).flag.sourceToPushout
        (QuillenStageShellData.ofStageThree B).flag.pushoutToQuotient
        (QuillenStageShellData.ofStageThree B).flag.source_pushoutToQuotient_zero) :=
  (QuillenStageShellData.ofStageThree B).flag.source_pushout_quotient_exact

example {n : ℕ} (A : Stage C (2 * n + 1)) :
    Stage C (edgewiseQ.obj ⦋n⦌).len :=
  edgewiseStageOfNat A

example {n : ℕ} (A : Stage C (2 * n + 1))
    (k l : Fin (n + 1)) (hkl : k ≤ l) :
    QuillenStageShellData C :=
  edgewiseStageShellPacketNat A k l hkl

section DegreeOne

variable (A : Stage C 3)

local notation "D" => edgewiseStageShellPacketNat A
  (0 : Fin 2) (1 : Fin 2) (by decide)

example : (D).flag.kernelObj =
    A.obj.obj (interval (0 : Fin 4) 1 (by decide)) := by
  rfl

example : (D).span.apex =
    A.obj.obj (interval (0 : Fin 4) 2 (by decide)) := by
  rfl

example : (D).target =
    A.obj.obj (interval (0 : Fin 4) 3 (by decide)) := by
  rfl

example : (D).source =
    A.obj.obj (interval (1 : Fin 4) 2 (by decide)) := by
  rfl

example : (D).flag.pushoutObj =
    A.obj.obj (interval (1 : Fin 4) 3 (by decide)) := by
  rfl

example : (D).flag.quotientObj =
    A.obj.obj (interval (2 : Fin 4) 3 (by decide)) := by
  rfl

end DegreeOne

example {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C (edgewiseQ.obj b).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellPacket
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A)
        k l hkl =
      edgewiseStageShellPacket A
        (α.toOrderHom k) (α.toOrderHom l)
        (α.toOrderHom.monotone hkl) :=
  edgewiseStageShellPacket_reindex α A k l hkl

/-- The collapsing degeneracy sends the shell `0 ≤ 1` to `0 ≤ 0`. -/
example (A : Stage C (edgewiseQ.obj ⦋0⦌).len) :
    edgewiseStageShellPacket
        ((reindexStage (C := C)
          (edgewiseQ.map (σ (0 : Fin 1)))).obj A)
        (0 : Fin 2) (1 : Fin 2) (by decide) =
      edgewiseStageShellPacket A
        (0 : Fin 1) (0 : Fin 1) le_rfl := by
  have h0 : (σ (0 : Fin 1)).toOrderHom (0 : Fin 2) = (0 : Fin 1) := by
    rfl
  have h1 : (σ (0 : Fin 1)).toOrderHom (1 : Fin 2) = (0 : Fin 1) := by
    rfl
  simpa only [h0, h1] using edgewiseStageShellPacket_reindex
    (C := C) (σ (0 : Fin 1)) A
    (0 : Fin 2) (1 : Fin 2) (by decide)

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).span ≅
      QuillenQ.underlyingIsoFwdSpan
        (eqToIso (edgewiseStageShellSourceEqTarget A k)) :=
  edgewiseStageShellSpanReflIso A k

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).quillenHom =
      (QuillenQ.underlyingIso
        (eqToIso (edgewiseStageShellSourceEqTarget A k))).hom :=
  edgewiseStageShellClass_eq_underlyingIso_hom A k

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).quillenHom ≫
        (QuillenQ.underlyingIso
          (eqToIso (edgewiseStageShellSourceEqTarget A k))).inv =
      𝟙 _ :=
  edgewiseStageShellClass_id A k

set_option maxHeartbeats 2000000
section Composition

variable (A : Stage C (edgewiseQ.obj ⦋2⦌).len)

local notation "k" => (0 : Fin 3)
local notation "l" => (1 : Fin 3)
local notation "r" => (2 : Fin 3)

local notation "hkl" => (show k ≤ l by decide)
local notation "hlr" => (show l ≤ r by decide)
local notation "hkr" => (show k ≤ r by decide)

noncomputable local instance compositionHasPullback :
    HasPullback
      (edgewiseStageShellPacket A k l hkl).span.r
      (edgewiseStageShellPacket A l r hlr).span.l :=
  (edgewiseStageShell_isPullback A hkl hlr).hasPullback

example :
    IsPullback
      (edgewiseStageShellToLeft A hkl hlr)
      (edgewiseStageShellToRight A hkl hlr)
      (edgewiseStageShellPacket A k l hkl).span.r
      (edgewiseStageShellPacket A l r hlr).span.l :=
  edgewiseStageShell_isPullback A hkl hlr

example :
    (edgewiseStageShellPacket A k r hkr).span ≅
      Span.comp (edgewiseStageShellPacket A k l hkl).span
        (edgewiseStageShellPacket A l r hlr).span :=
  edgewiseStageShellSpanCompIso A hkl hlr

example :
    (edgewiseStageShellSpanCompIso A hkl hlr).hom.hom ≫
        pullback.fst
          (edgewiseStageShellPacket A k l hkl).span.r
          (edgewiseStageShellPacket A l r hlr).span.l =
      edgewiseStageShellToLeft A hkl hlr :=
  edgewiseStageShellSpanCompIso_hom_fst A hkl hlr

example :
    (edgewiseStageShellSpanCompIso A hkl hlr).hom.hom ≫
        pullback.snd
          (edgewiseStageShellPacket A k l hkl).span.r
          (edgewiseStageShellPacket A l r hlr).span.l =
      edgewiseStageShellToRight A hkl hlr :=
  edgewiseStageShellSpanCompIso_hom_snd A hkl hlr

example :
    (edgewiseStageShellPacket A k l hkl).quillenHom ≫
        (edgewiseStageShellPacket A l r hlr).quillenHom =
      (edgewiseStageShellPacket A k r hkr).quillenHom :=
  edgewiseStageShellClass_comp A hkl hlr

end Composition

set_option maxHeartbeats 200000

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagStageShellTests

end
