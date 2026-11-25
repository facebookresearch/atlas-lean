/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlag
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagGridIndex
public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageIntervalRectangle
public import MathlibExt.CategoryTheory.Waldhausen.Exact

import MathlibExt.CategoryTheory.ExactCategory.Bicartesian

/-!
# Quillen span flags extracted from Stage shells

A four-vertex shell in an edgewise finite Waldhausen stage determines a raw
Quillen span and its literal six-cell exact flag.  Overlapping shells retain
the same Stage objects and maps.  For three ordered vertices, admissible
exactness identifies the long-shell apex with the pullback apex used by span
composition.

`QuillenStageShellData` stores only the material degree-three Stage.  Its
`source`, `target`, `span`, and `flag` accessors are reconstructed canonically
from that Stage, so a packet cannot carry unrelated span or flag data.

The rectangle pushout is flipped to the source-first/target-second
orientation of `QuillenSpanFlagData`.  No flag or grid is chosen from a
quotient class, and this file constructs no all-degree simplicial map,
realization, equivalence, additivity, or Q/S comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageShellWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

set_option linter.defProp false in
@[no_expose]
def stageMap_horiz_comp {n : ℕ} (B : Stage C n)
    {i j k l : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    (hkl : k ≤ l) :
    B.obj.map (horiz hij hjk) ≫
        B.obj.map (horiz (hij.trans hjk) hkl) =
      B.obj.map (horiz hij (hjk.trans hkl)) := by
  rw [← B.obj.map_comp]
  apply B.obj.congr_map
  apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

set_option linter.defProp false in
@[no_expose]
def stageMap_vert_comp {n : ℕ} (B : Stage C n)
    {i j k l : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    (hkl : k ≤ l) :
    B.obj.map (vert hij (hjk.trans hkl)) ≫
        B.obj.map (vert hjk hkl) =
      B.obj.map (vert (hij.trans hjk) hkl) := by
  rw [← B.obj.map_comp]
  apply B.obj.congr_map
  apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

/-- A degree-three Stage whose raw Quillen span and literal six-cell flag are
canonically derived from its cells and structure witnesses. -/
structure QuillenStageShellData (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] where
  /-- The material degree-three Stage. -/
  stage : Stage C 3

namespace QuillenStageShellData

/-- Source object of a Stage shell packet. -/
abbrev source (D : QuillenStageShellData C) : C :=
  D.stage.obj.obj (interval (1 : Fin 4) 2 (by decide))

/-- Target object of a Stage shell packet. -/
abbrev target (D : QuillenStageShellData C) : C :=
  D.stage.obj.obj (interval (0 : Fin 4) 3 (by decide))

/-- The middle raw span canonically determined by a Stage shell, from cell
`12` to cell `03` through cell `02`. -/
@[reducible]
noncomputable def span (D : QuillenStageShellData C) :
    QuillenSpan D.source D.target := by
  let B := D.stage
  let h01 : (0 : Fin 4) ≤ 1 := by decide
  let h12 : (1 : Fin 4) ≤ 2 := by decide
  let h23 : (2 : Fin 4) ≤ 3 := by decide
  let h02 : (0 : Fin 4) ≤ 2 := h01.trans h12
  let h03 : (0 : Fin 4) ≤ 3 := h02.trans h23
  have h012 := B.property.cofiber_triple h01 h12
  have h023 := B.property.cofiber_triple h02 h23
  let S012 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h01 h12))
      (B.obj.map (vert h01 h12)) h012.comp_eq_zero
  let S023 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h02 h23))
      (B.obj.map (vert h02 h23)) h023.comp_eq_zero
  have h012Exact : IsAdmissibleExact S012 :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S012) h012
  have h023Exact : IsAdmissibleExact S023 :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S023) h023
  exact
    { apex := B.obj.obj (interval 0 2 h02)
      l := B.obj.map (vert h01 h12)
      r := B.obj.map (horiz h02 h23)
      wl := ExactCategory.isAdmissibleEpi_g h012Exact
      wr := ExactCategory.isAdmissibleMono_f h023Exact }

/-- The literal six-cell flag canonically determined by a Stage shell. -/
@[reducible]
noncomputable def flag (D : QuillenStageShellData C) :
    QuillenSpanFlagData D.span := by
  let B := D.stage
  let h01 : (0 : Fin 4) ≤ 1 := by decide
  let h12 : (1 : Fin 4) ≤ 2 := by decide
  let h23 : (2 : Fin 4) ≤ 3 := by decide
  let h02 : (0 : Fin 4) ≤ 2 := h01.trans h12
  let h13 : (1 : Fin 4) ≤ 3 := h12.trans h23
  let h03 : (0 : Fin 4) ≤ 3 := h02.trans h23
  have h012 := B.property.cofiber_triple h01 h12
  have h013 := B.property.cofiber_triple h01 h13
  have h023 := B.property.cofiber_triple h02 h23
  have h123 := B.property.cofiber_triple h12 h23
  let S012 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h01 h12))
      (B.obj.map (vert h01 h12)) h012.comp_eq_zero
  let S013 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h01 h13))
      (B.obj.map (vert h01 h13)) h013.comp_eq_zero
  let S023 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h02 h23))
      (B.obj.map (vert h02 h23)) h023.comp_eq_zero
  let S123 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h12 h23))
      (B.obj.map (vert h12 h23)) h123.comp_eq_zero
  have h012Exact : IsAdmissibleExact S012 :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S012) h012
  have h013Exact : IsAdmissibleExact S013 :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S013) h013
  have h023Exact : IsAdmissibleExact S023 :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S023) h023
  have h123Exact : IsAdmissibleExact S123 :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S123) h123
  let S : QuillenSpan
      (B.obj.obj (interval 1 2 h12))
      (B.obj.obj (interval 0 3 h03)) := D.span
  have hHoriz013 :
      B.obj.map (horiz h01 h12) ≫ B.obj.map (horiz h02 h23) =
        B.obj.map (horiz h01 h13) :=
    stageMap_horiz_comp B h01 h12 h23
  have hVert023 :
      B.obj.map (vert h01 h13) ≫ B.obj.map (vert h12 h23) =
        B.obj.map (vert h02 h23) :=
    stageMap_vert_comp B h01 h12 h23
  have hKernelTargetZero :
      (B.obj.map (horiz h01 h12) ≫ S.r) ≫
          B.obj.map (vert h01 h13) = 0 := by
    rw [show S.r = B.obj.map (horiz h02 h23) from rfl,
      hHoriz013]
    exact h013.comp_eq_zero
  let T013 : ShortComplex C :=
    ShortComplex.mk (B.obj.map (horiz h01 h12) ≫ S.r)
      (B.obj.map (vert h01 h13)) hKernelTargetZero
  have hT013Exact : IsAdmissibleExact T013 := by
    let e : S013 ≅ T013 :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          simp only [S013, T013, Iso.refl_hom, Category.id_comp,
            Category.comp_id]
          rw [show S.r = B.obj.map (horiz h02 h23) from rfl]
          exact hHoriz013)
        (by simp [S013, T013])
    exact ExactCategory.isAdmissibleExact_of_iso e h013Exact
  change QuillenSpanFlagData S
  exact
    { kernelObj := B.obj.obj (interval 0 1 h01)
      pushoutObj := B.obj.obj (interval 1 3 h13)
      quotientObj := B.obj.obj (interval 2 3 h23)
      kernelι := B.obj.map (horiz h01 h12)
      quotientπ := B.obj.map (vert h02 h23)
      sourceToPushout := B.obj.map (horiz h12 h23)
      targetToPushout := B.obj.map (vert h01 h13)
      pushoutToQuotient := B.obj.map (vert h12 h23)
      kernel_left_zero := by
        simpa only [S] using h012.comp_eq_zero
      right_quotient_zero := by
        simpa only [S] using h023.comp_eq_zero
      pushoutSquare := by
        simpa only [S] using
          (B.property.isPushout_intervalRectangle h01 h12 h23).flip
      target_pushoutToQuotient := hVert023
      source_pushoutToQuotient_zero := h123.comp_eq_zero
      kernel_targetToPushout_zero := hKernelTargetZero
      kernel_apex_source_exact := by
        simpa only [S, S012] using h012Exact
      apex_target_quotient_exact := by
        simpa only [S, S023] using h023Exact
      kernel_target_pushout_exact := by
        simpa only [T013] using hT013Exact
      source_pushout_quotient_exact := by
        simpa only [S123] using h123Exact }

/-- Quotient-valued Quillen arrow represented by a Stage shell packet. -/
noncomputable def quillenHom (D : QuillenStageShellData C) :
    (⟨D.source⟩ : QuillenQ C) ⟶ ⟨D.target⟩ :=
  QuillenQ.mkHom D.span

/-- Canonical packet associated to a degree-three Stage. -/
@[reducible]
noncomputable def ofStageThree (B : Stage C 3) :
    QuillenStageShellData C :=
  { stage := B }

@[simp]
theorem ofStageThree_stage (B : Stage C 3) :
    (ofStageThree B).stage = B :=
  rfl

@[simp]
theorem ofStageThree_span_apex (B : Stage C 3) :
    (ofStageThree B).span.apex =
      B.obj.obj (interval (0 : Fin 4) 2 (by decide)) :=
  rfl

@[simp]
theorem ofStageThree_span_l (B : Stage C 3) :
    (ofStageThree B).span.l =
      B.obj.map (vert (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 2 by decide)) :=
  rfl

@[simp]
theorem ofStageThree_span_r (B : Stage C 3) :
    (ofStageThree B).span.r =
      B.obj.map (horiz (show (0 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_kernelObj (B : Stage C 3) :
    (ofStageThree B).flag.kernelObj =
      B.obj.obj (interval (0 : Fin 4) 1 (by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_pushoutObj (B : Stage C 3) :
    (ofStageThree B).flag.pushoutObj =
      B.obj.obj (interval (1 : Fin 4) 3 (by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_quotientObj (B : Stage C 3) :
    (ofStageThree B).flag.quotientObj =
      B.obj.obj (interval (2 : Fin 4) 3 (by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_kernelι (B : Stage C 3) :
    (ofStageThree B).flag.kernelι =
      B.obj.map (horiz (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 2 by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_quotientπ (B : Stage C 3) :
    (ofStageThree B).flag.quotientπ =
      B.obj.map (vert (show (0 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_sourceToPushout (B : Stage C 3) :
    (ofStageThree B).flag.sourceToPushout =
      B.obj.map (horiz (show (1 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_targetToPushout (B : Stage C 3) :
    (ofStageThree B).flag.targetToPushout =
      B.obj.map (vert (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 3 by decide)) :=
  rfl

@[simp]
theorem ofStageThree_flag_pushoutToQuotient (B : Stage C 3) :
    (ofStageThree B).flag.pushoutToQuotient =
      B.obj.map (vert (show (1 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)) :=
  rfl

theorem ofStageThree_flag_kernelι_comp_span_r (B : Stage C 3) :
    (ofStageThree B).flag.kernelι ≫ (ofStageThree B).span.r =
      B.obj.map (horiz (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 3 by decide)) := by
  exact stageMap_horiz_comp B (by decide) (by decide) (by decide)

end QuillenStageShellData

/-- Restrict an edgewise Stage to the shell determined by `k ≤ l`, retaining
its raw span and literal flag together. -/
@[reducible]
noncomputable def edgewiseStageShellPacket {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenStageShellData C :=
  QuillenStageShellData.ofStageThree
    ((reindexStage (C := C) (edgewiseShell a k l hkl)).obj A)

/-- Arithmetic adapter from `Stage C (2*n+1)` to the exact edgewise Stage
index used by reindexing. -/
noncomputable def edgewiseStageOfNat {n : ℕ}
    (A : Stage C (2 * n + 1)) :
    Stage C (edgewiseQ.obj ⦋n⦌).len := by
  simpa only [edgewiseQ_obj_len] using A

/-- Natural-number presentation of an edgewise Stage shell packet. -/
noncomputable def edgewiseStageShellPacketNat {n : ℕ}
    (A : Stage C (2 * n + 1))
    (k l : Fin (n + 1)) (hkl : k ≤ l) :
    QuillenStageShellData C :=
  edgewiseStageShellPacket (edgewiseStageOfNat A) k l hkl

@[simp]
theorem edgewiseStageShellPacket_stage {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket A k l hkl).stage =
      (reindexStage (C := C) (edgewiseShell a k l hkl)).obj A :=
  rfl

/-- Shell packets commute strictly with every edgewise Stage reindexing. -/
@[simp]
theorem edgewiseStageShellPacket_reindex
    {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C (edgewiseQ.obj b).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellPacket
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A)
        k l hkl =
      edgewiseStageShellPacket A
        (α.toOrderHom k) (α.toOrderHom l)
        (α.toOrderHom.monotone hkl) := by
  unfold edgewiseStageShellPacket
  rw [reindexStage_edgewiseShell_obj]

set_option linter.defProp false in
@[no_expose]
def edgewiseLeftIndex_anti {a : SimplexCategory}
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    edgewiseLeftIndex a l ≤ edgewiseLeftIndex a k := by
  have h := (edgewiseShell a k l hkl).toOrderHom.monotone
    (show (0 : Fin 4) ≤ 1 by decide)
  simpa only [edgewiseShell_zero, edgewiseShell_one] using h

set_option linter.defProp false in
@[no_expose]
def edgewiseLeftIndex_le_rightIndex (a : SimplexCategory)
    (k : Fin (a.len + 1)) :
    edgewiseLeftIndex a k ≤ edgewiseRightIndex a k := by
  have h := (edgewiseShell a k k le_rfl).toOrderHom.monotone
    (show (1 : Fin 4) ≤ 2 by decide)
  simpa only [edgewiseShell_one, edgewiseShell_two] using h

set_option linter.defProp false in
@[no_expose]
def edgewiseRightIndex_mono {a : SimplexCategory}
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    edgewiseRightIndex a k ≤ edgewiseRightIndex a l := by
  have h := (edgewiseShell a k l hkl).toOrderHom.monotone
    (show (2 : Fin 4) ≤ 3 by decide)
  simpa only [edgewiseShell_two, edgewiseShell_three] using h

set_option backward.isDefEq.respectTransparency false in
/-- Canonical map from the long-shell apex to the first short-shell apex. -/
@[reducible]
noncomputable def edgewiseStageShellToLeft {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (edgewiseStageShellPacket A k r (hkl.trans hlr)).span.apex ⟶
      (edgewiseStageShellPacket A k l hkl).span.apex := by
  let hLrLl := edgewiseLeftIndex_anti hlr
  let hLlLk := edgewiseLeftIndex_anti hkl
  let hLkRk := edgewiseLeftIndex_le_rightIndex a k
  let hLlRk := hLlLk.trans hLkRk
  change A.obj.obj (interval (edgewiseLeftIndex a r)
      (edgewiseRightIndex a k) _) ⟶
    A.obj.obj (interval (edgewiseLeftIndex a l)
      (edgewiseRightIndex a k) _)
  exact A.obj.map (vert hLrLl hLlRk)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical map from the long-shell apex to the second short-shell apex. -/
@[reducible]
noncomputable def edgewiseStageShellToRight {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (edgewiseStageShellPacket A k r (hkl.trans hlr)).span.apex ⟶
      (edgewiseStageShellPacket A l r hlr).span.apex := by
  let hLrLl := edgewiseLeftIndex_anti hlr
  let hLlLk := edgewiseLeftIndex_anti hkl
  let hLkRk := edgewiseLeftIndex_le_rightIndex a k
  let hRkRl := edgewiseRightIndex_mono hkl
  let hLrRk := hLrLl.trans (hLlLk.trans hLkRk)
  change A.obj.obj (interval (edgewiseLeftIndex a r)
      (edgewiseRightIndex a k) _) ⟶
    A.obj.obj (interval (edgewiseLeftIndex a r)
      (edgewiseRightIndex a l) _)
  exact A.obj.map (horiz hLrRk hRkRl)

set_option backward.isDefEq.respectTransparency false in
/-- The long-shell apex is the pullback of the two consecutive shell apices
over their common vertex. -/
theorem edgewiseStageShell_isPullback {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    IsPullback
      (edgewiseStageShellToLeft A hkl hlr)
      (edgewiseStageShellToRight A hkl hlr)
      (edgewiseStageShellPacket A k l hkl).span.r
      (edgewiseStageShellPacket A l r hlr).span.l := by
  let Lr := edgewiseLeftIndex a r
  let Ll := edgewiseLeftIndex a l
  let Lk := edgewiseLeftIndex a k
  let Rk := edgewiseRightIndex a k
  let Rl := edgewiseRightIndex a l
  let hLrLl : Lr ≤ Ll := edgewiseLeftIndex_anti hlr
  let hLlLk : Ll ≤ Lk := edgewiseLeftIndex_anti hkl
  let hLkRk : Lk ≤ Rk := edgewiseLeftIndex_le_rightIndex a k
  let hRkRl : Rk ≤ Rl := edgewiseRightIndex_mono hkl
  let hLlRk : Ll ≤ Rk := hLlLk.trans hLkRk
  let hLrRk : Lr ≤ Rk := hLrLl.trans hLlRk
  let hLlRl : Ll ≤ Rl := hLlRk.trans hRkRl
  let wS := (A.property.cofiber_triple hLrLl hLlRk).comp_eq_zero
  let wT := (A.property.cofiber_triple hLrLl hLlRl).comp_eq_zero
  let S : ShortComplex C :=
    ShortComplex.mk (A.obj.map (horiz hLrLl hLlRk))
      (A.obj.map (vert hLrLl hLlRk)) wS
  let T : ShortComplex C :=
    ShortComplex.mk (A.obj.map (horiz hLrLl hLlRl))
      (A.obj.map (vert hLrLl hLlRl)) wT
  have hS : IsAdmissibleExact S := by
    simpa only [S, wS] using
      ExactCategory.isAdmissibleExact_of_isCofibrationSequence
        (A.property.cofiber_triple hLrLl hLlRk)
  have hT : IsAdmissibleExact T := by
    simpa only [T, wT] using
      ExactCategory.isAdmissibleExact_of_isCofibrationSequence
        (A.property.cofiber_triple hLrLl hLlRl)
  have hFirst :
      A.obj.map (horiz hLrLl hLlRk) ≫
          edgewiseStageShellToRight A hkl hlr =
        A.obj.map (horiz hLrLl hLlRl) := by
    change A.obj.map (horiz hLrLl hLlRk) ≫
        A.obj.map (horiz hLrRk hRkRl) = _
    exact stageMap_horiz_comp A hLrLl hLlRk hRkRl
  have hRect :=
    A.property.isPushout_intervalRectangle hLrLl hLlRk hRkRl
  let φ : S ⟶ T :=
    ShortComplex.homMk (𝟙 _)
      (edgewiseStageShellToRight A hkl hlr)
      (edgewiseStageShellPacket A k l hkl).span.r
      (by simpa only [S, T, Category.id_comp] using hFirst.symm)
      (by
        change A.obj.map (horiz hLrRk hRkRl) ≫
            A.obj.map (vert hLrLl hLlRl) =
          A.obj.map (vert hLrLl hLlRk) ≫
            A.obj.map (horiz hLlRk hRkRl)
        exact hRect.w)
  let _ : IsIso φ.τ₁ := by
    change IsIso (𝟙 _)
    infer_instance
  have hpb :=
    ExactCategory.isPullback_g_of_isAdmissibleExact_of_isIso_left φ hS hT
  change IsPullback
    (edgewiseStageShellToLeft A hkl hlr)
    (edgewiseStageShellToRight A hkl hlr)
    (edgewiseStageShellPacket A k l hkl).span.r
    (edgewiseStageShellPacket A l r hlr).span.l at hpb
  exact hpb

noncomputable local instance edgewiseStageShell_hasPullback
    {a : SimplexCategory} (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    HasPullback
      (edgewiseStageShellPacket A k l hkl).span.r
      (edgewiseStageShellPacket A l r hlr).span.l :=
  (edgewiseStageShell_isPullback A hkl hlr).hasPullback

set_option backward.isDefEq.respectTransparency false in
/-- The long-to-left apex map followed by the first short-span left leg is
the long-span left leg. -/
theorem edgewiseStageShellToLeft_comp_l {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    edgewiseStageShellToLeft A hkl hlr ≫
        (edgewiseStageShellPacket A k l hkl).span.l =
      (edgewiseStageShellPacket A k r (hkl.trans hlr)).span.l := by
  let hLrLl := edgewiseLeftIndex_anti hlr
  let hLlLk := edgewiseLeftIndex_anti hkl
  let hLkRk := edgewiseLeftIndex_le_rightIndex a k
  change A.obj.map (vert hLrLl (hLlLk.trans hLkRk)) ≫
      A.obj.map (vert hLlLk hLkRk) =
    A.obj.map (vert (hLrLl.trans hLlLk) hLkRk)
  exact stageMap_vert_comp A hLrLl hLlLk hLkRk

set_option backward.isDefEq.respectTransparency false in
/-- The long-to-right apex map followed by the second short-span right leg
is the long-span right leg. -/
theorem edgewiseStageShellToRight_comp_r {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    edgewiseStageShellToRight A hkl hlr ≫
        (edgewiseStageShellPacket A l r hlr).span.r =
      (edgewiseStageShellPacket A k r (hkl.trans hlr)).span.r := by
  let hLrLl := edgewiseLeftIndex_anti hlr
  let hLlLk := edgewiseLeftIndex_anti hkl
  let hLkRk := edgewiseLeftIndex_le_rightIndex a k
  let hRkRl := edgewiseRightIndex_mono hkl
  let hRlRr := edgewiseRightIndex_mono hlr
  let hLrRk := hLrLl.trans (hLlLk.trans hLkRk)
  change A.obj.map (horiz hLrRk hRkRl) ≫
      A.obj.map (horiz (hLrRk.trans hRkRl) hRlRr) =
    A.obj.map (horiz hLrRk (hRkRl.trans hRlRr))
  exact stageMap_horiz_comp A hLrRk hRkRl hRlRr

set_option backward.isDefEq.respectTransparency false in
/-- The raw long-shell span is isomorphic to the chosen pullback composite
of its two consecutive short-shell spans. -/
noncomputable def edgewiseStageShellSpanCompIso {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (edgewiseStageShellPacket A k r (hkl.trans hlr)).span ≅
      Span.comp (edgewiseStageShellPacket A k l hkl).span
        (edgewiseStageShellPacket A l r hlr).span := by
  let hpb := edgewiseStageShell_isPullback A hkl hlr
  exact Span.mkIso hpb.isoPullback
    (by
      change hpb.isoPullback.hom ≫
          (pullback.fst _ _ ≫
            (edgewiseStageShellPacket A k l hkl).span.l) = _
      rw [← Category.assoc, hpb.isoPullback_hom_fst,
        edgewiseStageShellToLeft_comp_l])
    (by
      change hpb.isoPullback.hom ≫
          (pullback.snd _ _ ≫
            (edgewiseStageShellPacket A l r hlr).span.r) = _
      rw [← Category.assoc, hpb.isoPullback_hom_snd,
        edgewiseStageShellToRight_comp_r])

@[simp]
theorem edgewiseStageShellSpanCompIso_hom_fst {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (edgewiseStageShellSpanCompIso A hkl hlr).hom.hom ≫
        pullback.fst
          (edgewiseStageShellPacket A k l hkl).span.r
          (edgewiseStageShellPacket A l r hlr).span.l =
      edgewiseStageShellToLeft A hkl hlr := by
  exact (edgewiseStageShell_isPullback A hkl hlr).isoPullback_hom_fst

@[simp]
theorem edgewiseStageShellSpanCompIso_hom_snd {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (edgewiseStageShellSpanCompIso A hkl hlr).hom.hom ≫
        pullback.snd
          (edgewiseStageShellPacket A k l hkl).span.r
          (edgewiseStageShellPacket A l r hlr).span.l =
      edgewiseStageShellToRight A hkl hlr := by
  exact (edgewiseStageShell_isPullback A hkl hlr).isoPullback_hom_snd

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive shell classes compose to the long-shell class. -/
theorem edgewiseStageShellClass_comp {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (edgewiseStageShellPacket A k l hkl).quillenHom ≫
        (edgewiseStageShellPacket A l r hlr).quillenHom =
      (edgewiseStageShellPacket A k r (hkl.trans hlr)).quillenHom := by
  unfold QuillenStageShellData.quillenHom
  change quillenComp
      (QuillenQ.mkHom (edgewiseStageShellPacket A k l hkl).span)
      (QuillenQ.mkHom (edgewiseStageShellPacket A l r hlr).span) =
    QuillenQ.mkHom
      (edgewiseStageShellPacket A k r (hkl.trans hlr)).span
  rw [AlgebraicKTheory.mkHom_comp]
  exact (QuillenQ.mkHom_sound
    (edgewiseStageShellSpanCompIso A hkl hlr)).symm

set_option linter.defProp false in
@[no_expose]
def edgewiseStageShellApexIndexEqSource {a : SimplexCategory}
    (k : Fin (a.len + 1)) :
    (indexFunctor (edgewiseShell a k k le_rfl)).obj
        (interval (0 : Fin 4) 2 (by decide)) =
      (indexFunctor (edgewiseShell a k k le_rfl)).obj
        (interval (1 : Fin 4) 2 (by decide)) := by
  simp only [indexFunctor_obj_interval, edgewiseShell_zero,
    edgewiseShell_one, edgewiseShell_two]

set_option linter.defProp false in
@[no_expose]
def edgewiseStageShellSourceIndexEqTarget {a : SimplexCategory}
    (k : Fin (a.len + 1)) :
    (indexFunctor (edgewiseShell a k k le_rfl)).obj
        (interval (1 : Fin 4) 2 (by decide)) =
      (indexFunctor (edgewiseShell a k k le_rfl)).obj
        (interval (0 : Fin 4) 3 (by decide)) := by
  simp only [indexFunctor_obj_interval, edgewiseShell_zero,
    edgewiseShell_one, edgewiseShell_two, edgewiseShell_three]

set_option linter.defProp false in
@[no_expose]
def edgewiseStageShellApexIndexEqTarget {a : SimplexCategory}
    (k : Fin (a.len + 1)) :
    (indexFunctor (edgewiseShell a k k le_rfl)).obj
        (interval (0 : Fin 4) 2 (by decide)) =
      (indexFunctor (edgewiseShell a k k le_rfl)).obj
        (interval (0 : Fin 4) 3 (by decide)) :=
  (edgewiseStageShellApexIndexEqSource k).trans
    (edgewiseStageShellSourceIndexEqTarget k)

/-- In a repeated shell, the apex and source objects agree canonically. -/
theorem edgewiseStageShellApexEqSource {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).span.apex =
      (edgewiseStageShellPacket A k k le_rfl).source :=
  congrArg A.obj.obj (edgewiseStageShellApexIndexEqSource k)

/-- In a repeated shell, its source and target objects agree canonically. -/
theorem edgewiseStageShellSourceEqTarget {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).source =
      (edgewiseStageShellPacket A k k le_rfl).target :=
  congrArg A.obj.obj (edgewiseStageShellSourceIndexEqTarget k)

/-- In a repeated shell, the apex and target objects agree canonically. -/
theorem edgewiseStageShellApexEqTarget {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).span.apex =
      (edgewiseStageShellPacket A k k le_rfl).target :=
  congrArg A.obj.obj (edgewiseStageShellApexIndexEqTarget k)

set_option backward.isDefEq.respectTransparency false in
/-- The left leg of a repeated shell is the canonical equality transport. -/
theorem edgewiseStageShellSpan_refl_l {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).span.l =
      (eqToIso (edgewiseStageShellApexEqSource A k)).hom := by
  change A.obj.map ((indexFunctor (edgewiseShell a k k le_rfl)).map
      (vert (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 2 by decide))) =
    eqToHom (congrArg A.obj.obj
      (edgewiseStageShellApexIndexEqSource k))
  calc
    A.obj.map ((indexFunctor (edgewiseShell a k k le_rfl)).map
        (vert (show (0 : Fin 4) ≤ 1 by decide)
          (show (1 : Fin 4) ≤ 2 by decide))) =
      A.obj.map (eqToHom (edgewiseStageShellApexIndexEqSource k)) :=
        congrArg A.obj.map (by
          apply Arrow.hom_ext <;> exact Subsingleton.elim _ _)
    _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The right leg of a repeated shell is the canonical equality transport. -/
theorem edgewiseStageShellSpan_refl_r {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).span.r =
      (eqToIso (edgewiseStageShellApexEqTarget A k)).hom := by
  change A.obj.map ((indexFunctor (edgewiseShell a k k le_rfl)).map
      (horiz (show (0 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide))) =
    eqToHom (congrArg A.obj.obj
      (edgewiseStageShellApexIndexEqTarget k))
  calc
    A.obj.map ((indexFunctor (edgewiseShell a k k le_rfl)).map
        (horiz (show (0 : Fin 4) ≤ 2 by decide)
          (show (2 : Fin 4) ≤ 3 by decide))) =
      A.obj.map (eqToHom (edgewiseStageShellApexIndexEqTarget k)) :=
        congrArg A.obj.map (by
          apply Arrow.hom_ext <;> exact Subsingleton.elim _ _)
    _ = _ := by simp

/-- A repeated shell is isomorphic to the forward span of the canonical
source-to-target equality isomorphism. -/
noncomputable def edgewiseStageShellSpanReflIso {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).span ≅
      QuillenQ.underlyingIsoFwdSpan
        (eqToIso (edgewiseStageShellSourceEqTarget A k)) := by
  refine Span.mkIso
    (eqToIso (edgewiseStageShellApexEqSource A k)) ?_ ?_
  · change (eqToIso (edgewiseStageShellApexEqSource A k)).hom ≫ 𝟙 _ = _
    rw [Category.comp_id, edgewiseStageShellSpan_refl_l]
  · change (eqToIso (edgewiseStageShellApexEqSource A k)).hom ≫
        (eqToIso (edgewiseStageShellSourceEqTarget A k)).hom = _
    rw [edgewiseStageShellSpan_refl_r]
    simp

/-- The quotient class of a repeated shell is the canonical underlying
equality isomorphism. -/
theorem edgewiseStageShellClass_eq_underlyingIso_hom
    {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).quillenHom =
      (QuillenQ.underlyingIso
        (eqToIso (edgewiseStageShellSourceEqTarget A k))).hom := by
  unfold QuillenStageShellData.quillenHom
  rw [QuillenQ.underlyingIso_hom]
  exact QuillenQ.mkHom_sound (edgewiseStageShellSpanReflIso A k)

/-- After canonical endpoint normalization, a repeated shell is the identity
Quillen morphism. -/
theorem edgewiseStageShellClass_id {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k k le_rfl).quillenHom ≫
        (QuillenQ.underlyingIso
          (eqToIso (edgewiseStageShellSourceEqTarget A k))).inv =
      𝟙 _ := by
  rw [edgewiseStageShellClass_eq_underlyingIso_hom, Iso.hom_inv_id]

end AlgebraicKTheory

end
