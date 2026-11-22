/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The cyclic-wait fixture preserves the mathematical example in the public
Atlas PR #946 source, same-repository path
`CSLibExtTest/Languages/SessionTypes/CyclicTests.lean` (blob `801d13b1`).
Its finite-session codex/direct GPT proof lineage remains attributed under
the Meta license. The Lean test declarations are private, but the source is
public. These local consumers use the unchanged public finite typing API and
its polarized bridge; they do not redefine a session foundation.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.BinaryBridge
import CSLibExt.Languages.SessionTypes.Endpoint.Priority
import CSLibExt.Languages.SessionTypes.Endpoint.RankedTyping
import CSLibExt.Languages.SessionTypes.Endpoint.FrontierProgress
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant
import CSLibExt.Languages.PiCalculus.Behavioural

/-!
# The two-channel wait remains admitted by bare linear ownership

It must fail the separate dependency discipline. No enabled edge is assumed.
-/

namespace Cslib.SessionTypes.Endpoint.CyclicTests

open PiCalculus

/-- Wait for channel zero before using channel one. -/
def leftThread : Proc := .inp (.const 0) (.out (.const 1) (.const 7) .nil)

/-- Wait for channel one before using channel zero. -/
def rightThread : Proc := .inp (.const 1) (.out (.const 0) (.const 7) .nil)

/-- Opposite one-action protocols, with incompatible thread scheduling. -/
def context : Cslib.SessionTypes.Context := fun c =>
  if c = 0 then .recv .end else if c = 1 then .send .end else .end

/-- The unchanged finite API admits the left waiting order. -/
theorem left_typed : Cslib.SessionTypes.HasType 0 context leftThread := by
  refine Cslib.SessionTypes.HasType.inp (s := .end) (by rfl) ?_
  refine Cslib.SessionTypes.HasType.out (s := .end) (by rfl) trivial ?_
  apply Cslib.SessionTypes.HasType.nil
  intro c
  by_cases h₀ : c = 0 <;> by_cases h₁ : c = 1 <;>
    simp [Cslib.SessionTypes.advance, context, h₀, h₁]

/-- The public finite API also admits the right waiting order with dual protocols. -/
theorem right_typed :
    Cslib.SessionTypes.HasType 0 (Cslib.SessionTypes.dualContext context) rightThread := by
  refine Cslib.SessionTypes.HasType.inp (s := .end) (by rfl) ?_
  refine Cslib.SessionTypes.HasType.out (s := .end) (by rfl) trivial ?_
  apply Cslib.SessionTypes.HasType.nil
  intro c
  by_cases h₀ : c = 0 <;> by_cases h₁ : c = 1 <;>
    simp [Cslib.SessionTypes.advance, Cslib.SessionTypes.dualContext,
      context, SessionType.dual, h₀, h₁]

/-- The cyclic pair remains endpoint-typed after the finite resource bridge. -/
theorem endpoint_cycle_typed (rank : Nat → Nat) :
    ∃ bound, HasType 0
      (Context.ofFinite context bound .positive rank ∪
        Context.ofFinite (Cslib.SessionTypes.dualContext context) bound .negative rank)
      (Cslib.SessionTypes.represent (leftThread, rightThread)) :=
  binary_hasType ⟨left_typed, right_typed⟩ rank

/-- The cycle cannot reduce even up to arbitrary existing π congruence. -/
theorem cycle_no_step (q : Proc) :
    ¬ PiCalculus.Step (Cslib.SessionTypes.represent (leftThread, rightThread)) q := by
  apply not_step_of_no_output
  simp [Cslib.SessionTypes.represent, leftThread, rightThread, HasUnguardedOutput]

/-- No natural-number rank assignment permits both cyclic wait guards. -/
theorem cycle_rejects_priorities (rank : Nat → Nat) :
    ¬ (GuardMin (Context.ofFinite context 2 .positive rank) ⟨.const 0, .positive⟩ (rank 0) ∧
      GuardMin (Context.ofFinite (Cslib.SessionTypes.dualContext context) 2 .negative rank)
        ⟨.const 1, .negative⟩ (rank 1)) := by
  rintro ⟨hl, hr⟩
  have h₀₁ := hl ⟨.const 1, .positive⟩ ⟨rank 1, .sendName .done⟩
    (by simp [Context.lookup_ofFinite, context, Protocol.ofFinite])
    (by simp [Protocol.unfold]) (by decide)
  have h₁₀ := hr ⟨.const 0, .negative⟩ ⟨rank 0, .sendName .done⟩
    (by simp [Context.lookup_ofFinite, Cslib.SessionTypes.dualContext,
      context, SessionType.dual, Protocol.ofFinite])
    (by simp [Protocol.unfold]) (by decide)
  change rank 0 < rank 1 at h₀₁
  change rank 1 < rank 0 at h₁₀
  omega

/-- The full syntax-directed refinement cannot type both original cyclic
threads in their paired finite-bridge rank interfaces, for ANY rank assignment. -/
theorem cycle_refinement_rejected (rank : Nat → Nat) :
    ¬ (RankedType 0 (Context.ofFinite context 2 .positive rank) leftThread ∧
      RankedType 0 (Context.ofFinite (Cslib.SessionTypes.dualContext context) 2 .negative rank)
        rightThread) := by
  rintro ⟨hl, hr⟩
  obtain ⟨el, cl, hn, hc, hg⟩ := hl.inp_guard
  have hleft : GuardMin (Context.ofFinite context 2 .positive rank)
      ⟨.const 0, .positive⟩ (rank 0) := by
    cases el with
    | mk a r =>
      change a = .const 0 at hn
      subst a
      cases r with
      | negative => simp [Context.lookup_ofFinite] at hc
      | positive =>
        have he : cl = (⟨rank 0, .recvName .done⟩ : Capability) :=
          Context.unique hc (by simp [Context.lookup_ofFinite, context, Protocol.ofFinite])
        subst cl
        exact hg
  obtain ⟨er, cr, hn, hc, hg⟩ := hr.inp_guard
  have hright : GuardMin
      (Context.ofFinite (Cslib.SessionTypes.dualContext context) 2 .negative rank)
      ⟨.const 1, .negative⟩ (rank 1) := by
    cases er with
    | mk a r =>
      change a = .const 1 at hn
      subst a
      cases r with
      | positive => simp [Context.lookup_ofFinite] at hc
      | negative =>
        have he : cr = (⟨rank 1, .recvName .done⟩ : Capability) := Context.unique hc
          (by simp [Context.lookup_ofFinite, Cslib.SessionTypes.dualContext,
            context, SessionType.dual, Protocol.ofFinite])
        subst cr
        exact hg
  exact cycle_rejects_priorities rank ⟨hleft, hright⟩

/-- GENERAL frontier progress rejects the cyclic process in ANY balanced
ownership context, including arbitrary redistribution of roles between threads. -/
theorem cycle_any_balanced_refinement_rejected {n : Nat} {Δ : Context} (hb : Balanced Δ) :
    ¬ RankedType n Δ (Cslib.SessionTypes.represent (leftThread, rightThread)) := by
  intro ht
  have hf : GuardFrontier (Cslib.SessionTypes.represent (leftThread, rightThread)) :=
    GuardFrontier.par (GuardFrontier.inp _ _) (GuardFrontier.inp _ _)
  rcases hf.progress ht hb with hc | ⟨q, hs⟩
  · have hin : HasUnguardedInput (Cslib.SessionTypes.represent (leftThread, rightThread)) :=
      Or.inl trivial
    exact (input_cong hc).mp hin
  · exact cycle_no_step q hs

end Cslib.SessionTypes.Endpoint.CyclicTests
