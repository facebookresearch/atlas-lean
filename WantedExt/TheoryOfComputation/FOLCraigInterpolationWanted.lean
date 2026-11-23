/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Craig interpolation for first-order logic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Symbols
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.FOLCraigWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

/-- Craig interpolation for first-order logic: if the sentence `φ` semantically entails
the sentence `ψ`, there is an interpolant sentence `θ` entailed by `φ` and entailing
`ψ`, using only the function and relation symbols occurring in both `φ` and `ψ`
(`formulaSymbols`). The propositional case is proved in
`CSLibExt/Logics/Propositional/NaturalDeduction/Interpolation.lean`
(`exists_interpolant_cpl`), and the propositional-to-first-order bridge is in
`CSLibExt/Logics/FirstOrder/PropositionalBridge.lean`; the first-order proof must
additionally handle quantifiers, terms, and equality, e.g. via a Henkin
construction or via cut elimination and Maehara's lemma.
Source: W. Craig, "Three uses of the Herbrand-Gentzen theorem in relating model theory
and proof theory", Journal of Symbolic Logic 22 (1957), 269-285; see also H. Enderton,
A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §2.5. -/
public theorem_wanted fol_craig_interpolation {L : FirstOrder.Language}
    {φ ψ : L.Sentence}
    (h : ∀ (M : Type) [L.Structure M], (M ⊨ φ) → (M ⊨ ψ)) :
    ∃ θ : L.Sentence,
      (∀ (M : Type) [L.Structure M], (M ⊨ φ) → (M ⊨ θ)) ∧
        (∀ (M : Type) [L.Structure M], (M ⊨ θ) → (M ⊨ ψ)) ∧
        formulaSymbols θ ⊆ formulaSymbols φ ∩ formulaSymbols ψ

end Cslib.Logic.FOLCraigWanted
