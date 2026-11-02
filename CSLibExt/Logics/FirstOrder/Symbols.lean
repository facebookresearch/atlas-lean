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

/-- **Symbols of a term.** The set of symbols of a first-order language $L$ that occur in a
term $t$ (with free variables and possibly bound variables), defined by recursion on $t$: a
variable contributes no symbols, and $f(t_1, \dots, t_k)$ contributes the function symbol $f$
together with the symbols of the terms $t_i$. The result lies in the set of all symbols of $L$,
but only function symbols can occur in a term. -/
def termSymbols {n : ℕ} : L.Term (α ⊕ Fin n) → Set L.Symbols
  | .var _ => ∅
  | .func f ts => {Sum.inl ⟨_, f⟩} ∪ ⋃ i, termSymbols (ts i)

/-- **Symbols of a formula.** The set of function and relation symbols of a first-order
language $L$ that occur in a formula $\varphi$ (with free variables and possibly bound
variables), defined by recursion on $\varphi$: falsum $\bot$ contributes no symbols, an
equation $t_1 = t_2$ contributes the symbols of the terms $t_1$ and $t_2$, an atomic formula
$R(t_1, \dots, t_k)$ contributes $R$ together with the symbols of the terms $t_i$, an
implication $\varphi \to \psi$ contributes the symbols of $\varphi$ and of $\psi$, and
$\forall x\, \varphi$ contributes the symbols of $\varphi$. Variables and the equality sign
contribute nothing. -/
def formulaSymbols {n : ℕ} : L.BoundedFormula α n → Set L.Symbols
  | .falsum => ∅
  | .equal t₁ t₂ => termSymbols t₁ ∪ termSymbols t₂
  | .rel R ts => {Sum.inr ⟨_, R⟩} ∪ ⋃ i, termSymbols (ts i)
  | .imp φ ψ => formulaSymbols φ ∪ formulaSymbols ψ
  | .all φ => formulaSymbols φ

end Cslib.Logic.FOL
