/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractionFoldingPaperfoldingSumContFracRecursion
import Mathlib.Algebra.Group.Even
import MathlibExt.NumberTheory.ContinuedFractions.Folding

namespace MathlibExtTest.NumberTheory.ContinuedFractionFoldingPaperfoldingSumContFracRecursion

open MetaMathlibExt

-- With `xₖ = 2 * k + 2`, the integer part of `S` is `1`.
example : (GenContFract.of (∑' n,
    paperfoldingSumTerm (fun n => 2 * n + 2) n)).h = 1 :=
  (paperfoldingSum_contFrac_recursion (fun n => 2 * n + 2) rfl (fun k => by omega) 2).1

-- At stage `1` the word is `(1, 1, 3, 2)`, so the third partial quotient is `3`.
example : (GenContFract.of (∑' n,
    paperfoldingSumTerm (fun n => 2 * n + 2) n)).partDens.get? 2
    = some 3 := by
  have hw : paperfoldingContFracWord (fun n => 2 * n + 2) 1 = [1, 1, 3, 2] := rfl
  have h := (paperfoldingSum_contFrac_recursion (fun n => 2 * n + 2) rfl
    (fun k => by omega) 1).2 2 (by rw [hw]; decide)
  simp only [hw] at h
  simpa using h

-- At stage `2` the middle crease `x₂ - 1 = 5` sits at index `4`.
example : (GenContFract.of (∑' n,
    paperfoldingSumTerm (fun n => 2 * n + 2) n)).partDens.get? 4
    = some 5 := by
  have hw : paperfoldingContFracWord (fun n => 2 * n + 2) 2 =
      [1, 1, 3, 2, 5, 1, 1, 3, 1, 1] := rfl
  have h := (paperfoldingSum_contFrac_recursion (fun n => 2 * n + 2) rfl
    (fun k => by omega) 2).2 4 (by rw [hw]; decide)
  simp only [hw] at h
  simpa using h

-- At stage `2` the mirror half contributes the crease `3` at index `7`.
example : (GenContFract.of (∑' n,
    paperfoldingSumTerm (fun n => 2 * n + 2) n)).partDens.get? 7
    = some 3 := by
  have hw : paperfoldingContFracWord (fun n => 2 * n + 2) 2 =
      [1, 1, 3, 2, 5, 1, 1, 3, 1, 1] := rfl
  have h := (paperfoldingSum_contFrac_recursion (fun n => 2 * n + 2) rfl
    (fun k => by omega) 2).2 7 (by rw [hw]; decide)
  simp only [hw] at h
  simpa using h

end MathlibExtTest.NumberTheory.ContinuedFractionFoldingPaperfoldingSumContFracRecursion
