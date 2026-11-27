/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidIndexBinomidShiftImageInterEqZero

/-!
# Tests for intersections of shifted lex-minimal extensions

These tests show that a lex-minimal sequence whose one-place shift is lex-minimal
is zero, and that equal shifts by five and two places have zero preimages.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 6
(`integers-2024-A53-prop-6`).
-/

namespace MathlibExtTest.NumberTheory.BinomidIndexBinomidShiftImageInterEqZero

open MetaMathlibExt

example {η : ℕ → ℕ} (hη : IsLexMinimalExtension η)
    (hshift : IsLexMinimalExtension (binomidShift 1 η)) : η = fun _ => 0 := by
  have hmem : binomidShift 1 η ∈ binomidShift 0 '' {η | IsLexMinimalExtension η}
      ∩ binomidShift 1 '' {η | IsLexMinimalExtension η} :=
    ⟨⟨binomidShift 1 η, hshift, binomidShift_zero _⟩, ⟨η, hη, rfl⟩⟩
  rw [binomidShift_image_inter_eq_zero (by decide : 0 ≠ 1)] at hmem
  have hz := Set.mem_singleton_iff.mp hmem
  funext i
  simpa [binomidShift] using congrFun hz (i + 1)

example {η γ : ℕ → ℕ} (hη : IsLexMinimalExtension η) (hγ : IsLexMinimalExtension γ)
    (h : binomidShift 5 η = binomidShift 2 γ) :
    η = (fun _ => 0) ∧ γ = (fun _ => 0) := by
  have hmem : binomidShift 5 η ∈ binomidShift 5 '' {η | IsLexMinimalExtension η}
      ∩ binomidShift 2 '' {η | IsLexMinimalExtension η} :=
    ⟨⟨η, hη, rfl⟩, ⟨γ, hγ, h.symm⟩⟩
  rw [binomidShift_image_inter_eq_zero (by decide : 5 ≠ 2)] at hmem
  have hz := Set.mem_singleton_iff.mp hmem
  constructor
  · funext i
    simpa [binomidShift] using congrFun hz (i + 5)
  · funext i
    simpa [binomidShift] using congrFun (h.symm.trans hz) (i + 2)

end MathlibExtTest.NumberTheory.BinomidIndexBinomidShiftImageInterEqZero
