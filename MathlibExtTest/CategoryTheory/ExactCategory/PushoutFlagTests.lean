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

import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag

/-!
# Exact pushout flag completion tests

Focused public-API checks for the induced quotient map, its two pushout-leg
computations, and the two completed admissible exact rows.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace MathlibExtTest.CategoryTheory.ExactCategory.PushoutFlagTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {K A X Y P Q : C}
variable (i : K ⟶ A) (p : A ⟶ X) (r : A ⟶ Y) (q : Y ⟶ Q)
  (x : X ⟶ P) (y : Y ⟶ P)
variable (wi : i ≫ p = 0) (wr : r ≫ q = 0)
variable (hL : IsAdmissibleExact (ShortComplex.mk i p wi))
  (hR : IsAdmissibleExact (ShortComplex.mk r q wr))
variable (sq : IsPushout p r x y)

/-- The square orientation is left-then-bottom equals top-then-right. -/
example : p ≫ x = r ≫ y := sq.w

/-- The induced quotient map has the expected source and target. -/
noncomputable example : P ⟶ Q :=
  pushoutQuotientMap p r q x y wr sq

/-- The induced quotient map kills the left pushout leg. -/
example : x ≫ pushoutQuotientMap p r q x y wr sq = 0 :=
  pushoutQuotientMap_x p r q x y wr sq

/-- The induced quotient map restricts to the original right quotient. -/
example : y ≫ pushoutQuotientMap p r q x y wr sq = q :=
  pushoutQuotientMap_y p r q x y wr sq

/-- The completed lower-left row is admissible exact. -/
example :
    IsAdmissibleExact
      (ShortComplex.mk (i ≫ r) y (by
        rw [Category.assoc, ← sq.w, ← Category.assoc, wi, zero_comp])) :=
  isAdmissibleExact_comp_pushout i p r q x y wi wr hL hR sq

/-- The completed lower-right row is admissible exact. -/
example :
    IsAdmissibleExact
      (ShortComplex.mk x (pushoutQuotientMap p r q x y wr sq)
        (pushoutQuotientMap_x p r q x y wr sq)) :=
  isAdmissibleExact_pushoutQuotientMap p r q x y wr hR sq

end MathlibExtTest.CategoryTheory.ExactCategory.PushoutFlagTests
