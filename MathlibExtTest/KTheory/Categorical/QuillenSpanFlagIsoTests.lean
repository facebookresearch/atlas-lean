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

import MathlibExt.KTheory.Exact.Quillen.SpanFlagIso

/-!
# Quillen span flag isomorphism-transport tests

Focused checks for the apex-isomorphism orientation, retained cells and
primitive maps, transported pushout square, and all four admissible exact
rows. No quotient descent or transport functoriality is tested or claimed.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open AlgebraicKTheory

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagIsoTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {X Y : C} {S S' : QuillenSpan X Y}
variable (e : S ≅ S') (D : QuillenSpanFlagData S)

/-- Kernel inclusion uses the forward apex isomorphism; every other primitive
map is retained. -/
example :
    (QuillenSpanFlagData.transport e D).kernelι =
        D.kernelι ≫ (Span.SpanBicat.apexIso e).hom ∧
      (QuillenSpanFlagData.transport e D).quotientπ = D.quotientπ ∧
      (QuillenSpanFlagData.transport e D).sourceToPushout =
        D.sourceToPushout ∧
      (QuillenSpanFlagData.transport e D).targetToPushout =
        D.targetToPushout ∧
      (QuillenSpanFlagData.transport e D).pushoutToQuotient =
        D.pushoutToQuotient := by
  simp

/-- Kernel, pushout, and quotient objects are retained in that order. -/
example :
    (QuillenSpanFlagData.transport e D).kernelObj = D.kernelObj ∧
      (QuillenSpanFlagData.transport e D).pushoutObj = D.pushoutObj ∧
      (QuillenSpanFlagData.transport e D).quotientObj = D.quotientObj := by
  simp

/-- The transported pushout square is based on the target span legs. -/
example :
    IsPushout S'.l S'.r
      (QuillenSpanFlagData.transport e D).sourceToPushout
      (QuillenSpanFlagData.transport e D).targetToPushout :=
  (QuillenSpanFlagData.transport e D).pushoutSquare

/-- All four exact rows are transported with their literal target-span maps. -/
example :
    IsAdmissibleExact
        (ShortComplex.mk (QuillenSpanFlagData.transport e D).kernelι S'.l
          (QuillenSpanFlagData.transport e D).kernel_left_zero) ∧
      IsAdmissibleExact
        (ShortComplex.mk S'.r
          (QuillenSpanFlagData.transport e D).quotientπ
          (QuillenSpanFlagData.transport e D).right_quotient_zero) ∧
      IsAdmissibleExact
        (ShortComplex.mk
          ((QuillenSpanFlagData.transport e D).kernelι ≫ S'.r)
          (QuillenSpanFlagData.transport e D).targetToPushout
          (QuillenSpanFlagData.transport e D).kernel_targetToPushout_zero) ∧
      IsAdmissibleExact
        (ShortComplex.mk
          (QuillenSpanFlagData.transport e D).sourceToPushout
          (QuillenSpanFlagData.transport e D).pushoutToQuotient
          (QuillenSpanFlagData.transport e D).source_pushoutToQuotient_zero) :=
  ⟨(QuillenSpanFlagData.transport e D).kernel_apex_source_exact,
    (QuillenSpanFlagData.transport e D).apex_target_quotient_exact,
    (QuillenSpanFlagData.transport e D).kernel_target_pushout_exact,
    (QuillenSpanFlagData.transport e D).source_pushout_quotient_exact⟩

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagIsoTests
