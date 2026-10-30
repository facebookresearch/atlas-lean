/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.PCF.Soundness
public import CSLibExtTest.Languages.LambdaCalculus.PCF.BigStepTests

/-!
# Tests for the denotational semantics of PCF

* Denotations of arithmetic, the zero test, and abstraction, computed with the
  constructor equations.
* Soundness on the evaluated programs of `BigStepTests`: `ifz`, one unfolding
  of `fix`, and the recursive `countdown`.
* The diverging `Ω := fix (λx : nat. x)` denotes `⊥`, the least fixed point of
  the identity; `succ Ω` denotes no number, and `ifz Ω zero zero` denotes `⊥`
  (the zero test is strict).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF.Tests

open scoped CslibStlc
open OmegaCompletePartialOrder Tm

/-- The empty environment. -/
abbrev ε : Env [] := PUnit.unit

example : denote (.pred (.succ .zero) : Tm [] .nat) ε = Part.some 0 := rfl

/-- `ifz zero 2 zero`, computed from the denotation alone. -/
theorem ifzZeroTwo_denote : denote (.ifz .zero (numeral 2) .zero : Tm [] .nat) ε = Part.some 2 := by
  rw [denote_ifz, denote_zero, Part.bind_some]
  exact denote_numeral ε 2

/-- The identity function denotes the identity. -/
example (d : Ty.dom .nat) :
    denote (.lam (.var .zero) : Tm [] (Ty.nat ⇒ Ty.nat)) ε d = d := rfl

example : denote ifzExample ε = Part.some 1 := ifzExample_eval.denote_numeral ε

example : denote fixZero ε = Part.some 0 := fixZero_eval.denote_numeral (n := 0) ε

example : denote (.app countdown (numeral 1)) ε = Part.some 0 :=
  countdown_one.denote_numeral (n := 0) ε

/-- `Ω := fix (λx : nat. x)`. -/
def omega : Tm [] .nat := .fix (.lam (.var .zero))

/-- `Ω` denotes `⊥`: the least fixed point of the identity. -/
theorem omega_denote : denote omega ε = ⊥ := by
  rw [omega, denote_fix]
  exact le_antisymm (ContinuousHom.lfp_le _ le_rfl) bot_le

/-- `succ Ω` denotes no number. -/
example (n : ℕ) : n ∉ (denote (.succ omega) ε : Part ℕ) := by
  change n ∉ (denote omega ε : Part ℕ).map Nat.succ
  rw [omega_denote]
  change n ∉ Part.map Nat.succ (Part.none : Part ℕ)
  simp

/-- The zero test is strict: `ifz Ω zero zero` denotes `⊥`, although both
branches denote `0`. -/
example : denote (.ifz omega .zero .zero) ε = ⊥ := by
  rw [denote_ifz, omega_denote]
  exact Part.bind_none _

end Cslib.Languages.LambdaCalculus.PCF.Tests
