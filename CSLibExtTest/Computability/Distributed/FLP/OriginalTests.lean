/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.FLP.Original

/-!
# Tests for the original FLP theorem

The hypotheses of `flp_original` are satisfiable. In the algorithm `leader0` on two processes,
process `0` decides its input bit when it receives it and process `1` never decides. It is
partially correct: only process `0` ever decides, so no state has two decision values, and
each value is decided from the input that gives it to process `0`. The theorem then yields an
admissible run that never decides (in fact the run in which process `0` never receives its
input is one).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.FLP.OriginalTests

open Cslib.FLP

/-- Process `0` decides the input bit it receives; process `1` never decides. -/
def leader0 : Algorithm (Fin 2) Unit Unit where
  init _ := ()
  next _ _ := ()
  send _ _ := 0
  out m _ := if m.dest = 0 then
      match m.msg with
      | .inl b => some b
      | .inr _ => none
    else none

/-- Process `1` never decides. -/
theorem proc_one_undecided {inp : Fin 2 → Bool} {s : State (Fin 2) Unit Unit}
    (hs : leader0.Reachable inp s) : (s.proc 1).out = none := by
  obtain ⟨xs, h⟩ := hs
  have inv : leader0.lts.TrInv (fun s : State (Fin 2) Unit Unit => (s.proc 1).out = none) := by
    intro s x s' htr hs
    cases x with
    | none => exact (Algorithm.tr_none htr) ▸ hs
    | some m =>
        obtain ⟨-, rfl⟩ := htr
        simp only [Algorithm.recvMsg]
        split_ifs with h₁ h₂
        · simp [leader0, ← h₁]
        · simpa [← h₁] using hs
        · exact hs
  exact LTS.mtrInv_of_trInv inv _ _ _ h (by simp [Algorithm.start])

/-- `leader0` satisfies agreement. -/
theorem leader0_agreed (inp : Fin 2 → Bool) (s : State (Fin 2) Unit Unit)
    (hs : leader0.Reachable inp s) : s.Agreed := by
  rintro b b' ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  have h1 := proc_one_undecided hs
  have hp0 : p = 0 := by
    by_contra h
    have : p = 1 := by omega
    simp [State.ProcDecided, this, h1] at hp
  have hq0 : q = 0 := by
    by_contra h
    have : q = 1 := by omega
    simp [State.ProcDecided, this, h1] at hq
  subst hp0 hq0
  simp only [State.ProcDecided] at hp hq
  rw [hp] at hq
  exact Option.some.inj hq

/-- Each value is decided in some reachable state of `leader0`. -/
theorem leader0_val (b : Bool) :
    ∃ inp s, leader0.Reachable inp s ∧ s.Decided b := by
  let m : Message (Fin 2) Unit := ⟨0, .inl b⟩
  have hm : m ∈ (leader0.start fun _ => b).msgs := by simp [Algorithm.start, m]
  refine ⟨fun _ => b, leader0.recvMsg m (leader0.start fun _ => b),
    ⟨[some m], LTS.MTr.single (lts := leader0.lts) ⟨hm, rfl⟩⟩, 0, ?_⟩
  simp [State.ProcDecided, Algorithm.recvMsg, Algorithm.start, leader0, m]

/-- The original FLP theorem applies to `leader0`. -/
example : ∃ inp ss xs, leader0.AdmissibleRun inp 1 ss xs ∧ ∀ k b, ¬ (ss k).Decided b :=
  flp_original (by simp) leader0 leader0_agreed leader0_val

end Cslib.Distributed.FLP.OriginalTests
