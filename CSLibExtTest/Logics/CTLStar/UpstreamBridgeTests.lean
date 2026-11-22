/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math,
CSLibExtTest/Logics/CTLStar/UpstreamBridgeTests.lean,
commit cbe67c4f99b625a43c98959d53f88f7b137d7119 (PR 10058).
Original formalization by Adam Kiezun.
-/
module

public import CSLibExt.Logics.CTLStar.UpstreamBridge

/-!
# Tests for the CTL* state-run/labeled-execution bridge

`E G F p` holds at `false` in the toggle system by the state-run proof
`toggle_egf_p`; the bridge transfers it to the canonical labeled-execution
presentation, and the path version transfers the alternating run's
satisfaction to the equivalent ω-sequence presentation.
-/

@[expose] public section

namespace Cslib.CTLStar.UpstreamBridge.Tests

/-- `E G F p` holds at `false` in the canonical labeled-execution presentation. -/
example : UpstreamStateSat (toggleLTS) toggleValuation
    (.exists (.alwaysPath (.until (.state .top) (.state (.atom ()))))) false :=
  (stateSat_iff_upstream _ _).mp toggle_egf_p

/-- The alternating run satisfies `G F p` in the equivalent ω-sequence presentation. -/
example : UpstreamPathSat (toggleLTS) toggleValuation
    (.alwaysPath (.until (.state .top) (.state (.atom ())))) ⟨toggleRun⟩ := by
  rw [← pathSat_iff_upstream _ (fun i => ⟨(), rfl⟩)]
  rw [pathSat_always]
  intro i
  cases hi : toggleRun i with
  | true =>
      refine ⟨0, ?_, fun j _ => True.intro⟩
      rw [pathSat_state]
      simp only [shiftSeq_apply_zero]
      exact hi
  | false =>
      refine ⟨1, ?_, fun j _ => True.intro⟩
      rw [pathSat_state, Semantics.shiftSeq_add, shiftSeq_apply_zero]
      change !toggleRun i = true
      rw [hi]
      rfl

end Cslib.CTLStar.UpstreamBridge.Tests
