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

import MathlibExt.KTheory.Exact.Quillen.SpanFlag

/-!
# Quillen span six-cell flag tests

Focused checks for existence, pushout orientation, quotient-map equations,
the canonical induced map, and the four literal admissible exact sequences.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open AlgebraicKTheory

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {X Y : C} (S : QuillenSpan X Y)

/-- Every raw admissible span has flag data, without exposing a chosen
witness. -/
example : Nonempty (QuillenSpanFlagData S) :=
  QuillenSpanFlagData.nonempty S

variable (D : QuillenSpanFlagData S)

/-- The three added cells lie in the original exact category. -/
example : C × C × C := (D.kernelObj, D.pushoutObj, D.quotientObj)

/-- The pushout square retains the reviewed left/right-leg orientation. -/
example : S.l ≫ D.sourceToPushout = S.r ≫ D.targetToPushout :=
  D.pushoutSquare.w

/-- The two quotient-map computations retain source-zero and target-quotient
order. -/
example :
    D.sourceToPushout ≫ D.pushoutToQuotient = 0 ∧
      D.targetToPushout ≫ D.pushoutToQuotient = D.quotientπ :=
  ⟨D.source_pushoutToQuotient_zero, D.target_pushoutToQuotient⟩

/-- The stored quotient map is the canonical map induced by the pushout. -/
example :
    D.pushoutToQuotient =
      pushoutQuotientMap S.l S.r D.quotientπ D.sourceToPushout
        D.targetToPushout D.right_quotient_zero D.pushoutSquare :=
  D.pushoutToQuotient_eq

/-- All four literal rows have the intended admissible exact structures. -/
example :
    IsAdmissibleExact
        (ShortComplex.mk D.kernelι S.l D.kernel_left_zero) ∧
      IsAdmissibleExact
        (ShortComplex.mk (D.kernelι ≫ S.r) D.targetToPushout
          D.kernel_targetToPushout_zero) ∧
      IsAdmissibleExact
        (ShortComplex.mk S.r D.quotientπ D.right_quotient_zero) ∧
      IsAdmissibleExact
        (ShortComplex.mk D.sourceToPushout D.pushoutToQuotient
          D.source_pushoutToQuotient_zero) :=
  ⟨D.kernel_apex_source_exact, D.kernel_target_pushout_exact,
    D.apex_target_quotient_exact, D.source_pushout_quotient_exact⟩

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagTests
