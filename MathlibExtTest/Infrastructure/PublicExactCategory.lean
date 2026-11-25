/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.KTheory.Exact.K0.Basic

/-!
# Focused exact-category public API checks

These examples also occur in the whole-root integration check. Focused imports
keep their per-change checks independent of unrelated MathlibExt domains.
-/

open CategoryTheory Limits

universe v u

example (C : Type u) [Category.{v} C] [Abelian C] : ExactCategory C := inferInstance

example {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (X Y : C) :
    AlgebraicKTheory.K0.mk (X ⊞ Y) =
      AlgebraicKTheory.K0.mk X + AlgebraicKTheory.K0.mk Y := by
  simp
