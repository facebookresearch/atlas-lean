/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Reductions
public import CSLibExt.Computability.Decidability.RiceApplications

@[expose] public section

/-!
# Tests for Rice's theorem and the Sipser §5.1 reductions
-/

set_option autoImplicit false

open Cslib.Decidability
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.Reductions

/-- Rice for languages: "the domain contains `0`" is undecidable (the identity halts on `0`, a
code defined nowhere does not). -/
example : ¬TM2Decidable fun c : Code ↦ 0 ∈ c.eval.Dom := by
  obtain ⟨e, he⟩ := exists_code_empty
  exact not_tm2Decidable_language {S | 0 ∈ S} (c₁ := Code.id) (c₂ := e)
    (by simp [PFun.dom_eq, Code.eval_id]) (by simp [he])

/-- The chain A_TM ≤ HALT_TM ≤ (regular halting sets), and undecidability of all three. -/
example : ManyOneReducible Accepts RegularDomainCode :=
  manyOneReducible_accepts_halts.trans manyOneReducible_halts_regularDomain

example : ¬TM2Decidable Accepts ∧ ¬TM2Decidable Halts ∧ ¬TM2Decidable RegularDomainCode :=
  ⟨not_tm2Decidable_accepts, not_tm2Decidable_halts, not_tm2Decidable_regularDomain⟩

/-- The identity accepts `0`. -/
example : Accepts (Code.id, 0) := by simp [Accepts, Code.eval_id]

/-- Every word over `Unit` is in the unary language of `ℕ`. -/
example : [(), (), ()] ∈ unaryLang Set.univ := trivial

end CSLibExtTest.Computability.Decidability.Reductions
