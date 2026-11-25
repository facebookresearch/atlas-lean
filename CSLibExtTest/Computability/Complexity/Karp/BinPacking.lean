/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.BinPacking

/-!
# Tests for the bin packing decision problem

The completeness theorem applies to the standard complexity classes, including the exact
language used for empty bins and repeated item sizes.
-/

namespace CSLibExtTest.Computability.Complexity.Karp.BinPacking

open MetaMathlibExt.BitstringEncoding
open MetaMathlibExt.Complexity.NPComplete.BinPacking
open MetaMathlibExt.ComplexityTheory

example : binPackingDec ∈ NP :=
  binPacking_npComplete.1

example (L : DecisionProblem) (h : L ∈ NP) :
    Cslib.CookLevin.PolyManyOneRed L binPackingDec :=
  binPacking_npComplete.2 L h

example : binPackingDec (bitEncode (α := BinPackingInstance) ([2, 2], 2, 3)) = true := by
  classical
  rw [binPackingDec, bitDecode_bitEncode, decide_eq_true_eq]
  refine ⟨[[2], [2], []], rfl, by simp, ?_⟩
  simp

example : binPackingDec (bitEncode (α := BinPackingInstance) ([0], 0, 0)) = false := by
  rw [binPackingDec, bitDecode_bitEncode, decide_eq_false_iff_not]
  rintro ⟨bins, h, hf, _⟩
  have he : bins = [] := List.length_eq_zero_iff.mp h
  simp [he] at hf

example : binPackingDec [true] = false := rfl

end CSLibExtTest.Computability.Complexity.Karp.BinPacking
