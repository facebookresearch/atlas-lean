/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.HopcroftWork
public import Cslib.Algorithms.Lean.TimeM

/-!
# Hopcroft predecessor-work instrumentation in the canonical `TimeM`

This instruments the existing execution with exactly the event measure
`hopcroftCost`. A batch of predecessor visits is charged by its size,
plus one unit per popped splitter. The return value is exactly the
existing `hopcroftLoop` result.

`TimeM.time` here is predecessor-work, NOT Lean evaluation time or a RAM
runtime certificate. All List/Finset scans, membership tests, allocation,
and initialization are outside this event model. In particular, computing
`preimage` by filtering all states is not a constant-time operation. This
instrumentation does not silently change that implementation or claim an
efficient indexed implementation.
-/

@[expose] public section

namespace DFA.Hopcroft

open Cslib.Algorithms.Lean

variable {α σ : Type*} [FinEnum α] [Fintype σ] [DecidableEq σ]

/-- The actual loop with predecessor-visit and pop events recorded in
CSLib's `TimeM`. Pure scans are not charged in this event model. -/
def hopcroftLoopWork (M : DFA α σ) : ℕ → List (Finset σ) →
    List (Finset σ × α) →
      TimeM ℕ (List (Finset σ) × List (Finset σ × α))
  | 0, P, W => pure (P, W)
  | _ + 1, P, [] => pure (P, [])
  | k + 1, P, (C, a) :: W => do
      TimeM.tick ((preimage M C a).card + 1)
      hopcroftLoopWork M k (roundP M P C a) (roundW M P W C a)

/-- Instrumentation preserves the exact loop result. -/
@[simp]
theorem hopcroftLoopWork_ret (M : DFA α σ) (k : ℕ)
    (P : List (Finset σ)) (W : List (Finset σ × α)) :
    (hopcroftLoopWork M k P W).ret = M.hopcroftLoop k P W := by
  induction k generalizing P W with
  | zero => rfl
  | succ k ih =>
    cases W with
    | nil => rfl
    | cons cb W =>
      obtain ⟨C, a⟩ := cb
      simpa [hopcroftLoopWork, hopcroftLoop] using
        ih (roundP M P C a) (roundW M P W C a)

/-- The recorded cost is exactly the work of the actual popped trace. -/
@[simp]
theorem hopcroftLoopWork_time (M : DFA α σ) (k : ℕ)
    (P : List (Finset σ)) (W : List (Finset σ × α)) :
    (hopcroftLoopWork M k P W).time =
      hopcroftCost M (hopcroftSplitters M k P W) := by
  induction k generalizing P W with
  | zero => rfl
  | succ k ih =>
    cases W with
    | nil => rfl
    | cons cb W =>
      obtain ⟨C, a⟩ := cb
      simp [hopcroftLoopWork, hopcroftSplitters, ih, hopcroftCost]

/-- The canonical cost monad records the proved total predecessor-work
bound for every initialized execution prefix. -/
theorem hopcroftLoopWork_init_le [Fintype α] (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (k : ℕ) :
    (hopcroftLoopWork M k (initP M) (initW M)).time ≤
      2 * Fintype.card α * Fintype.card σ *
        (Nat.log 2 (Fintype.card σ) + 1) := by
  rw [hopcroftLoopWork_time]
  exact hopcroftCost_init_trace_le M k

/-- At the proved terminating fuel, instrumentation returns the original
correct minimization partition and an empty waiting list. -/
theorem hopcroftLoopWork_complete_ret [Fintype α] (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] :
    (hopcroftLoopWork M (Fintype.card α * (Fintype.card σ + 1))
      (initP M) (initW M)).ret = (M.hopcroftPartition, []) := by
  rw [hopcroftLoopWork_ret]
  exact Prod.ext rfl (hopcroftLoop_waiting_eq_nil M)

end DFA.Hopcroft
