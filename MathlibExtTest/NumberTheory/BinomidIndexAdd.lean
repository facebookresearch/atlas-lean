/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidIndexAdd

/-!
# Tests for addition of lex-minimal extensions

The addition theorem applies to the zero sequence and to sums of three lex-minimal extensions.

Source: Jonathan Caalim and Yu-ichi Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 1.
-/

namespace MathlibExtTest.NumberTheory.BinomidIndexAdd

open MetaMathlibExt

example : IsLexMinimalExtension ((fun _ => 0) + (fun _ => 0)) :=
  IsLexMinimalExtension.add ⟨0, isLexMinimalExtensionOf_zero 0⟩
    ⟨0, isLexMinimalExtensionOf_zero 0⟩

example {η₁ η₂ η₃ : ℕ → ℕ} (h₁ : IsLexMinimalExtension η₁)
    (h₂ : IsLexMinimalExtension η₂) (h₃ : IsLexMinimalExtension η₃) :
    IsLexMinimalExtension (η₁ + η₂ + η₃) :=
  (h₁.add h₂).add h₃

end MathlibExtTest.NumberTheory.BinomidIndexAdd
