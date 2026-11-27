/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Exact.Quillen.SpanFlagGridIndex

/-!
# Edgewise shell-index tests

The tests pin both blocks, the degree-one middle face, literal shell
reindexing, a collapsing degeneracy, and Stage restriction.  They construct
no span, flag, quotient class, realization, additivity, or Q/S comparison.
-/

open CategoryTheory Limits
open scoped Simplicial

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagGridIndexTests

open SimplexCategory

example : (edgewiseLeftIndex ⦋1⦌ (0 : Fin 2)).val = 1 := by simp
example : (edgewiseLeftIndex ⦋1⦌ (1 : Fin 2)).val = 0 := by simp
example : (edgewiseRightIndex ⦋1⦌ (0 : Fin 2)).val = 2 := by simp
example : (edgewiseRightIndex ⦋1⦌ (1 : Fin 2)).val = 3 := by simp

/-- The reviewed degree-one middle face selects indices `1,2`. -/
example :
    ((edgewiseQ.map (δ (1 : Fin 2))).toOrderHom
      (edgewiseLeftIndex ⦋0⦌ (0 : Fin 1))).val = 1 := by
  rw [edgewiseQ_map_δ_leftIndex]
  simp

example :
    ((edgewiseQ.map (δ (1 : Fin 2))).toOrderHom
      (edgewiseRightIndex ⦋0⦌ (0 : Fin 1))).val = 2 := by
  rw [edgewiseQ_map_δ_rightIndex]
  simp

example {a b : SimplexCategory} (α : a ⟶ b)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseShell a k l hkl ≫ edgewiseQ.map α =
      edgewiseShell b (α.toOrderHom k) (α.toOrderHom l)
        (α.toOrderHom.monotone hkl) :=
  edgewiseShell_comp_edgewiseQ_map α k l hkl

example {n : ℕ} (q : Fin (n + 2))
    (k l : Fin (n + 1)) (hkl : k ≤ l) :
    edgewiseShell ⦋n⦌ k l hkl ≫ edgewiseQ.map (δ q) =
      edgewiseShell ⦋n + 1⦌ (q.succAbove k) (q.succAbove l)
        ((Fin.succAboveOrderEmb q).monotone hkl) :=
  edgewiseShell_comp_edgewiseQ_map_δ q k l hkl

/-- Degeneracy `σ 0` collapses the interval `0 ≤ 1` to `0 ≤ 0`. -/
example :
    edgewiseShell ⦋1⦌ (0 : Fin 2) (1 : Fin 2) (by decide) ≫
        edgewiseQ.map (σ (0 : Fin 1)) =
      edgewiseShell ⦋0⦌ (0 : Fin 1) (0 : Fin 1) le_rfl := by
  simpa using edgewiseShell_comp_edgewiseQ_map_σ
    (0 : Fin 1) (0 : Fin 2) (1 : Fin 2) (by decide)

universe v u

namespace Stage

open CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example {a b : SimplexCategory} (α : a ⟶ b)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    reindexStage (C := C) (edgewiseQ.map α) ⋙
        reindexStage (C := C) (edgewiseShell a k l hkl) =
      reindexStage (C := C)
        (edgewiseShell b (α.toOrderHom k) (α.toOrderHom l)
          (α.toOrderHom.monotone hkl)) :=
  reindexStage_edgewiseShell α k l hkl

example {a b : SimplexCategory} (α : a ⟶ b)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l)
    (A : Stage C (edgewiseQ.obj b).len) :
    (reindexStage (C := C) (edgewiseShell a k l hkl)).obj
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) =
      (reindexStage (C := C)
        (edgewiseShell b (α.toOrderHom k) (α.toOrderHom l)
          (α.toOrderHom.monotone hkl))).obj A :=
  reindexStage_edgewiseShell_obj α k l hkl A

end Stage

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagGridIndexTests
