/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

import MathlibExt.KTheory.Exact.K0.Basic
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Zero objects in exact `K₀`

Focused public-API checks that zero objects have vanishing `K₀` class and that
an exact category consisting entirely of zero objects has subsingleton `K₀`.
-/

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.KTheory.Exact.K0.ZeroObjectTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Any zero object represents the zero class. -/
example {X : C} (hX : IsZero X) :
    AlgebraicKTheory.K0.mk X = 0 :=
  AlgebraicKTheory.K0.mk_eq_zero_of_isZero hX

/-- If every object is zero, the exact `K₀` group is subsingleton. -/
example (h : ∀ X : C, IsZero X) :
    Subsingleton (AlgebraicKTheory.K0 C) :=
  AlgebraicKTheory.K0.subsingleton_of_forall_isZero h

/-- Concrete application to the zero `ℚ`-module. -/
example :
    (AlgebraicKTheory.K0.mk (ModuleCat.of ℚ PUnit) :
      AlgebraicKTheory.K0 (ModuleCat ℚ)) = 0 :=
  AlgebraicKTheory.K0.mk_eq_zero_of_isZero (ModuleCat.isZero_of_subsingleton _)

end MathlibExtTest.KTheory.Exact.K0.ZeroObjectTests
