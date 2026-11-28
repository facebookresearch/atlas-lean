/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidIndexBinomidAverageCondition

namespace MathlibExtTest.NumberTheory.BinomidIndexBinomidAverageCondition

open MetaMathlibExt

/-- The zero sequence satisfies the Average Condition through its lex-minimality. -/
example : BinomidAverageCondition (fun _ => 0) :=
  IsLexMinimalExtension.binomidAverageCondition ⟨0, isLexMinimalExtensionOf_zero 0⟩

/-- The upper average of the zero sequence is zero, as witnessed by its lex-minimality. -/
example : binomidUpperAverage (fun _ => 0) = 0 := by
  obtain ⟨i, _, heq⟩ :=
    IsLexMinimalExtension.binomidAverageCondition ⟨0, isLexMinimalExtensionOf_zero 0⟩
  have havg : binomidAverage (fun _ => 0) i = 0 := by simp [binomidAverage]
  rw [heq, havg]
  norm_cast

end MathlibExtTest.NumberTheory.BinomidIndexBinomidAverageCondition
