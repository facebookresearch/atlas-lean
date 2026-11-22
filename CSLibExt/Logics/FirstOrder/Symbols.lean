/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Symbols occurring in a first-order term or formula
-/
module

public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Syntax

/-!
# Symbols occurring in a first-order term or formula

The vocabulary of a term or formula, as a set of `FirstOrder.Language.Symbols`:
a function symbol contributes `Sum.inl ⟨n, f⟩`, a relation symbol contributes
`Sum.inr ⟨n, R⟩`. Free and bound variables contribute nothing. This is the
vocabulary relation Craig interpolation and Beth definability are stated with:
an interpolant may use only symbols occurring in both premises, and an explicit
definiens may not use the implicitly defined symbol.

## References

- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, §2.1
  (vocabulary of a formula) and §2.5 (Craig interpolation), §2.6 (Beth definability).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language} {α : Type*}

/-- The function and relation symbols occurring in a term. -/
def termSymbols {n : ℕ} : L.Term (α ⊕ Fin n) → Set L.Symbols
  | .var _ => ∅
  | .func f ts => {Sum.inl ⟨_, f⟩} ∪ ⋃ i, termSymbols (ts i)

/-- The function and relation symbols occurring in a formula. -/
def formulaSymbols {n : ℕ} : L.BoundedFormula α n → Set L.Symbols
  | .falsum => ∅
  | .equal t₁ t₂ => termSymbols t₁ ∪ termSymbols t₂
  | .rel R ts => {Sum.inr ⟨_, R⟩} ∪ ⋃ i, termSymbols (ts i)
  | .imp φ ψ => formulaSymbols φ ∪ formulaSymbols ψ
  | .all φ => formulaSymbols φ

end Cslib.Logic.FOL
