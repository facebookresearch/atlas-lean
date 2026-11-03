/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Substitution

/-!
# Substitution with an existing opposite endpoint on the sent physical name
-/

namespace Cslib.SessionTypes.Endpoint.SubstitutionTests

open PiCalculus

private def sending : Capability := ⟨0, .sendName .done⟩
private def receiving : Capability := ⟨0, .recvName .done⟩
private def peerContext : Context := Finmap.singleton ⟨.var 0, .negative⟩ receiving

/-- Before substitution, the received role and the existing peer have different
binder indices. Their roles, not their physical-name text, determine ownership. -/
def body : Proc := .par (.out (.var 0) (.const 7) .nil) (.inp (.var 1) .nil)

/-- The receive body has one new role and exactly the lifted pre-existing peer. -/
theorem body_typed : HasType 2
    ((Context.lift 0 peerContext).insert ⟨.var 0, .positive⟩ sending) body := by
  change HasType 2
    (Finmap.singleton (⟨.var 0, .positive⟩ : Key) sending ∪
      Finmap.singleton ⟨.var 1, .negative⟩ receiving) _
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · apply HasType.outName (e := ⟨.var 0, .positive⟩) (c := sending) (s := .done)
    · simp
    · rfl
    · change 0 < 2
      decide
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact HasType.nil_singleton (by change 0 < 2; decide)
  · apply HasType.inpName (e := ⟨.var 1, .negative⟩) (c := receiving) (s := .done)
    · simp
    · rfl
    · change 1 < 2
      decide
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact HasType.nil_singleton (by change 2 < 3; decide)

/-- Receiving the positive role while already owning the negative role is
legal: substitution places BOTH roles on one physical name without collision. -/
theorem opposite_roles_same_name_typed : HasType 1
    (peerContext.insert ⟨.var 0, .positive⟩ sending)
    (.par (.out (.var 0) (.const 7) .nil) (.inp (.var 0) .nil)) := by
  apply HasType.subst_endpoint body_typed
  · change 0 < 1
    decide
  · simp [peerContext, Finmap.mem_singleton]

/-- The receiver's already-existing peer still synchronizes with the
substituted role on their common physical channel. -/
theorem opposite_roles_same_name_step : PiCalculus.Step
    (.par (.out (.var 0) (.const 7) .nil) (.inp (.var 0) .nil)) (.par .nil .nil) := by
  exact PiCalculus.Step.commSelect (.refl _) (.refl _)

end Cslib.SessionTypes.Endpoint.SubstitutionTests
