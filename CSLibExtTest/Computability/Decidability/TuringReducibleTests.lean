/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.TuringReducible

@[expose] public section

/-!
# Tests for Turing reducibility between sets of naturals
-/

set_option autoImplicit false

open scoped Computability
open Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability.TuringReducible

/-- The characteristic function takes the value `1` on members and `0` elsewhere. -/
example : 1 ∈ charFun (fun n ↦ n = 3) 3 ∧ 0 ∈ charFun (fun n ↦ n = 3) 4 := by
  simp

example : charFun (fun n ↦ n = 3) 3 = Part.some 1 := charFun_of_pos rfl

/-- The empty set is decidable. -/
theorem computablePred_false : ComputablePred fun _ : ℕ ↦ False :=
  ComputablePred.computable_iff.mpr ⟨fun _ ↦ false, Computable.const false, by funext; simp⟩

/-- The halting set is not Turing reducible to the empty set. -/
example : ¬charFun haltingSet ≤ᵀ charFun fun _ ↦ False :=
  not_turingReducible_halting computablePred_false

/-- A set Turing reducible to the empty set is decidable. -/
example {p : ℕ → Prop} (h : charFun p ≤ᵀ charFun fun _ ↦ False) : ComputablePred p :=
  ComputablePred.of_turingReducible h computablePred_false

/-- The complement of the halting set is Turing reducible to it, but not many-one reducible. -/
example : charFun (fun n ↦ ¬haltingSet n) ≤ᵀ charFun haltingSet ∧
    ¬(fun n ↦ ¬haltingSet n) ≤₀ haltingSet :=
  ⟨(turingEquivalent_charFun_not haltingSet).1, not_manyOneReducible_not_halting⟩

/-- Many-one reductions are Turing reductions. -/
example (p : ℕ → Prop) : charFun p ≤ᵀ charFun p :=
  turingReducible_of_manyOneReducible (manyOneReducible_refl p)

end CSLibExtTest.Computability.Decidability.TuringReducible
