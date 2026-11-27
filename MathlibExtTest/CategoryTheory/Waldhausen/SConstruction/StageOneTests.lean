/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOne

/-!
# Canonical degree-one stage consumer tests

Focused downstream checks for the public `StageOne` API: the bundled
`stageOne` object's diagonal and `(0, 1)` interval values, plus one
orientation-sensitive horizontal computation. No new API, equivalence,
simplicial object, nerve, realization, or K/G-theory definition.
-/

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageOneTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Bundled `stageOne` object sends every diagonal to zero. -/
example (X : C) (i : Fin 2) :
    ((stageOne C).obj X).obj.obj (diag i) = (0 : C) :=
  stageOne_obj_diag C X i

/-- Bundled `stageOne` object sends the `(0, 1)` interval to `X`. -/
example (X : C) (h : (0 : Fin 2) ≤ 1) :
    ((stageOne C).obj X).obj.obj (interval 0 1 h) = X :=
  stageOne_obj_interval_zero_one C X h

/-- Orientation-sensitive horizontal `(0, 0, 1)` leg is the zero-to-`X` map. -/
example (X : C) (h00 : (0 : Fin 2) ≤ 0) (h01 : (0 : Fin 2) ≤ 1) :
    (stageOneDiagram C X).map (horiz h00 h01) = (isZero_zero C).to_ X :=
  stageOneDiagram_horiz_zero_zero_one C X h00 h01

/-- Bundled `stageOne` map at the `(0, 1)` interval is the input morphism. -/
example (X Y : C) (f : X ⟶ Y) :
    ((stageOne C).map f).hom.app (interval (0 : Fin 2) 1 (by decide)) = f :=
  stageOne_map_interval_zero_one C f

/-- Non-diagonal `Ar 1` object is the `(0, 1)` interval. -/
example (A : Ar 1) (hne : ¬ A.left = A.right) : A.left = 0 ∧ A.right = 1 :=
  ar1_zero_one_of_ne hne

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageOneTests
