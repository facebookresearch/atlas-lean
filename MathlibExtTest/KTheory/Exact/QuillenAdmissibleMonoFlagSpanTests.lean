/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoFlagSpan

/-! # Tests for Quillen spans from admissible-mono flags -/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction
open AlgebraicKTheory

universe v u

namespace MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoFlagSpan

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  [CategoryTheory.ExactCategory C]
  {n : ℕ} (F : AdmissibleMonoFlag C n)

#check AdmissibleMonoFlag.intervalQuillenSpan
#check AdmissibleMonoFlag.intervalQuillenSpan_apex
#check AdmissibleMonoFlag.intervalQuillenSpan_l
#check AdmissibleMonoFlag.intervalQuillenSpan_r
#check AdmissibleMonoFlag.intervalMap_self
#check AdmissibleMonoFlag.intervalQuotient_isZero_of_isIso

example {a b c d : Fin (n + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    QuillenSpan
      (F.intervalQuotient b c hbc)
      (F.intervalQuotient a d ((hab.trans hbc).trans hcd)) :=
  F.intervalQuillenSpan hab hbc hcd

#print axioms AdmissibleMonoFlag.intervalQuillenSpan

end MathlibExtTest.AlgebraicKTheory.QuillenAdmissibleMonoFlagSpan

end
