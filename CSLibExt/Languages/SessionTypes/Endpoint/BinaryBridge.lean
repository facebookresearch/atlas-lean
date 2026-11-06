/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.FiniteTyping
public import CSLibExt.Languages.SessionTypes.Communication

/-!
# Original binary configurations in finite polarized ownership

Neither the original protocol nor the existing π representation is changed.
Both original communication orientations have the same ownership bridge.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Binary session typing embeds into polarized endpoint typing.**
Dual original threads embed as disjoint opposite roles on the same
physical constants, with exactly their original finite protocol obligations. -/
theorem binary_hasType {Γ : Cslib.SessionTypes.Context} {r : Proc × Proc}
    (hr : Cslib.SessionTypes.BinaryTyped Γ r) (rank : Nat → Nat) :
    ∃ bound, HasType 0
      (Context.ofFinite Γ bound .positive rank ∪
        Context.ofFinite (Cslib.SessionTypes.dualContext Γ) bound .negative rank)
      (Cslib.SessionTypes.represent r) := by
  obtain ⟨bound, hb⟩ := hr.1.finite_support
  have hd : ∀ c, bound ≤ c → Cslib.SessionTypes.dualContext Γ c = .end := by
    intro c hc
    simp [Cslib.SessionTypes.dualContext, hb c hc, SessionType.dual]
  refine ⟨bound, HasType.par ?_ (HasType.ofFinite hr.1 bound hb .positive rank)
    (HasType.ofFinite hr.2 bound hd .negative rank)⟩
  exact Context.disjoint_ofFinite _ _ _ _ _ _ (by decide) _ _

end Cslib.SessionTypes.Endpoint
