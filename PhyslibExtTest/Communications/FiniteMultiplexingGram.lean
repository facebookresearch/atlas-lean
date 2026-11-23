/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.FiniteMultiplexingGram
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Communications.FiniteMultiplexingGram

namespace PhyslibExtTest.Communications.FiniteMultiplexingGram

/-- The skew pair has Gram entry `G 0 1 = (√2)⁻¹`: the concrete
nonorthogonal interference term. -/
example : Matrix.gram ℂ skewPair 0 1 = ((Real.sqrt 2)⁻¹ : ℂ) :=
  gram_skewPair_zero_one

/-- Each skew-pair waveform has unit norm. -/
example : ‖skewPair 0‖ = 1 ∧ ‖skewPair 1‖ = 1 :=
  ⟨norm_skewPair 0, norm_skewPair 1⟩

/-- With both symbols present, the first matched output is the
desired symbol plus the Gram interference term. -/
example : matchedOutput skewPair ![1, 1] 0 = 1 + ((Real.sqrt 2)⁻¹ : ℂ) := by
  simpa using skewPair_matchedOutput_zero ![1, 1]

/-- The Gram identity on the skew pair: matched outputs are the
Gram matrix times the symbol vector. -/
example (a : Fin 2 → ℂ) :
    matchedOutput skewPair a = (Matrix.gram ℂ skewPair).mulVec a :=
  matchedOutput_eq_gram_mulVec skewPair a

/-- FDMA with two distinct carriers recovers both symbols. -/
example (a : Fin 2 → ℂ) : matchedOutput (fun j => fdmaCarrier 4 (![1, 3] j)) a = a :=
  fdma_two_carriers_matchedOutput_eq a

/-- CDMA with the two orthonormal codes recovers both symbols. -/
example (a : Fin 2 → ℂ) : matchedOutput cdmaCode a = a :=
  cdma_matchedOutput_eq a

end PhyslibExtTest.Communications.FiniteMultiplexingGram
