/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Whole native undercategory functors retain original functor equality

The actual native Under.post codomain depends on the original functor's
object image. Whole original functor equality therefore gives genuine
heterogeneous equality of the SAME native undercategory functors. This
retains both entire original arrow maps and all triangle equations.
-/

universe u v w z
open CategoryTheory

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D] {X : C}

/-- The SAME native whole undercategory functors have heterogeneous equality under an actual
full original functor
equality. -/
theorem post_hcongr {F G : C ⥤ D} (h : F = G) : post (X := X) F ≍ post (X := X) G := by
  cases h
  rfl

end CategoryTheory.Under
