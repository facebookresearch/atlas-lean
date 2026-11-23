/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

Changes to this source code are licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.RelatesInSteps

/-! # Output reachability with time and resource bounds

Adapted from `eth/proof/statements/StepMachineStatements.lean` and
`eth/proof/machines/StepMachines/Prog/Stepped.lean` in `anthropics/formal-math`,
commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.

Finite paths use CSLib's `Relation.RelatesWithinSteps`. A transition consumes
one step only while the output is `none`; iteration leaves halted states fixed.
The explicit measure bounds every visited state, including the terminal state.
The state, input and output types may be infinite. All functions and the measure
are arbitrary; these abstract bounds imply no Turing time or computability claim.

Authors: Codex GPT-6.1-Sol
-/

@[expose] public section

namespace Cslib.OutputReachability

variable {State Output Input : Type*}

/-- One iteration, preserving a state once its output is available. -/
def next (step : State → State) (out : State → Option Output) (s : State) : State :=
  match out s with
  | some _ => s
  | none => step s

/-- An active step with a resource bound on its source. -/
def boundedStep (step : State → State) (out : State → Option Output)
    (measure : State → ℕ) (S : ℕ) (s t : State) : Prop :=
  out s = none ∧ measure s ≤ S ∧ t = step s

/-- Reach an output in at most `T` active steps, with every state bounded by `S`. -/
def ReachesOutput (step : State → State) (out : State → Option Output)
    (measure : State → ℕ) (s : State) (T S : ℕ) (b : Output) : Prop :=
  ∃ t, Relation.RelatesWithinSteps (boundedStep step out measure S) s t T ∧
    out t = some b ∧ measure t ≤ S

/-- Reach an output starting from an input's initial state. -/
def Runs (init : Input → State) (step : State → State) (out : State → Option Output)
    (measure : State → ℕ) (a : Input) (T S : ℕ) (b : Output) : Prop :=
  ReachesOutput step out measure (init a) T S b

variable {step : State → State} {out : State → Option Output}
  {measure : State → ℕ} {s t : State} {T S : ℕ} {b : Output}

@[simp] theorem next_of_none (h : out s = none) : next step out s = step s := by
  simp [next, h]

@[simp] theorem next_of_some (h : out s = some b) : next step out s = s := by
  simp [next, h]

/-- Every iterate of an already halted state is that state. -/
theorem iterate_of_some (h : out s = some b) (n : ℕ) : (next step out)^[n] s = s := by
  exact Function.iterate_fixed (next_of_some h) n

/-- A halted state reaches its output with any remaining time budget. -/
theorem ReachesOutput.halt (ho : out s = some b) (hs : measure s ≤ S) :
    ReachesOutput step out measure s T S b :=
  ⟨s, ⟨0, Nat.zero_le T, .refl s⟩, ho, hs⟩

/-- Prepend an active bounded step to a successful computation. -/
theorem ReachesOutput.prepend (ho : out s = none) (hs : measure s ≤ S)
    (h : ReachesOutput step out measure (step s) T S b) :
    ReachesOutput step out measure s (T + 1) S b := by
  obtain ⟨t, ⟨n, hn, hp⟩, ht, hm⟩ := h
  exact ⟨t, ⟨n + 1, Nat.succ_le_succ hn,
    hp.head s (step s) t n ⟨ho, hs, rfl⟩⟩, ht, hm⟩

/-- A canonical finite path ending in an output has the source's all-iterate bounds. -/
theorem relatesInSteps_iterate {n : ℕ}
    (h : Relation.RelatesInSteps (boundedStep step out measure S) s t n)
    (ho : out t = some b) (hs : measure t ≤ S) :
    (∀ T, n ≤ T → out ((next step out)^[T] s) = some b) ∧
      ∀ k, measure ((next step out)^[k] s) ≤ S := by
  induction h using Relation.RelatesInSteps.head_induction_on with
  | hrefl =>
    exact ⟨fun T _ => by rw [iterate_of_some ho, ho],
      fun k => by rwa [iterate_of_some ho]⟩
  | @hhead a c n he hp ih =>
    obtain ⟨ha, hm, rfl⟩ := he
    refine ⟨fun T hT => ?_, fun k => ?_⟩
    · obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      rw [Function.iterate_succ_apply, next_of_none ha]
      exact ih.1 T' (by omega)
    · cases k with
      | zero => exact hm
      | succ k =>
        rw [Function.iterate_succ_apply, next_of_none ha]
        exact ih.2 k

/-- Reachability gives stable outputs after the budget and bounds every iterate. -/
theorem ReachesOutput.iterate (h : ReachesOutput step out measure s T S b) :
    (∀ U, T ≤ U → out ((next step out)^[U] s) = some b) ∧
      ∀ n, measure ((next step out)^[n] s) ≤ S := by
  obtain ⟨t, ⟨n, hn, hp⟩, ho, hs⟩ := h
  obtain ⟨hout, hmeasure⟩ := relatesInSteps_iterate hp ho hs
  exact ⟨fun U hU => hout U (by omega), hmeasure⟩

/-- The source iteration condition constructs a canonical bounded path. -/
theorem reachesOutput_of_iterate
    (ho : out ((next step out)^[T] s) = some b)
    (hs : ∀ n, measure ((next step out)^[n] s) ≤ S) :
    ReachesOutput step out measure s T S b := by
  induction T generalizing s with
  | zero => exact .halt ho (hs 0)
  | succ T ih =>
    cases h : out s with
    | some b' =>
      rw [iterate_of_some h, h] at ho
      exact .halt (h.trans ho) (hs 0)
    | none =>
      apply ReachesOutput.prepend h (hs 0)
      apply ih
      · rwa [Function.iterate_succ_apply, next_of_none h] at ho
      · intro n
        have hn := hs (n + 1)
        rwa [Function.iterate_succ_apply, next_of_none h] at hn

/-- Exact source characterization, including bounds on all natural-number iterates. -/
theorem reachesOutput_iff_iterate :
    ReachesOutput step out measure s T S b ↔
      out ((next step out)^[T] s) = some b ∧
        ∀ n, measure ((next step out)^[n] s) ≤ S :=
  ⟨fun h => ⟨h.iterate.1 T (by omega), h.iterate.2⟩,
    fun ⟨ho, hs⟩ => reachesOutput_of_iterate ho hs⟩

/-- A terminal iterate remains unchanged at every later iteration count. -/
theorem iterate_stable (ho : out ((next step out)^[T] s) = some b)
    {U : ℕ} (hU : T ≤ U) : (next step out)^[U] s = (next step out)^[T] s := by
  rw [show U = (U - T) + T by omega, Function.iterate_add_apply,
    iterate_of_some ho]

/-- Finite visited-state bounds are equivalent to all-iterate bounds after halting. -/
theorem reachesOutput_iff_bounded_iterate :
    ReachesOutput step out measure s T S b ↔
      out ((next step out)^[T] s) = some b ∧
        ∀ n ≤ T, measure ((next step out)^[n] s) ≤ S := by
  rw [reachesOutput_iff_iterate]
  constructor
  · exact fun ⟨ho, hs⟩ => ⟨ho, fun n _ => hs n⟩
  · rintro ⟨ho, hs⟩
    refine ⟨ho, fun n => ?_⟩
    by_cases hn : n ≤ T
    · exact hs n hn
    · rw [iterate_stable ho (by omega)]
      exact hs T (by omega)

/-- Increasing either bound preserves reachability. -/
theorem ReachesOutput.mono {U R : ℕ} (h : ReachesOutput step out measure s T S b)
    (hT : T ≤ U) (hS : S ≤ R) : ReachesOutput step out measure s U R b := by
  obtain ⟨t, hp, ho, hs⟩ := h
  have hmap : Relation.RelatesWithinSteps (boundedStep step out measure R) s t T :=
    hp.map id (fun _ _ he => ⟨he.1, he.2.1.trans hS, he.2.2⟩)
  exact ⟨t, hmap.mono hT, ho, hs.trans hS⟩

/-- Output values reached from the same state are unique, regardless of bounds. -/
theorem ReachesOutput.unique {U R : ℕ} {c : Output}
    (h : ReachesOutput step out measure s T S b)
    (h' : ReachesOutput step out measure s U R c) : b = c := by
  have hb := h.iterate.1 (max T U) (by omega)
  have hc := h'.iterate.1 (max T U) (by omega)
  exact Option.some.inj (hb.symm.trans hc)

/-- Iteration initialized by an input, with absorbing halting. -/
def run (init : Input → State) (step : State → State) (out : State → Option Output)
    (a : Input) (n : ℕ) : State := (next step out)^[n] (init a)

/-- The source `Runs` interface, stated using initialized iteration. -/
theorem runs_iff_iterate {init : Input → State} {a : Input} :
    Runs init step out measure a T S b ↔
      out (run init step out a T) = some b ∧
        ∀ n, measure (run init step out a n) ≤ S :=
  reachesOutput_iff_iterate

/-- The output of a successful initialized run is present at every later time. -/
theorem Runs.out_run {init : Input → State} {a : Input}
    (h : Runs init step out measure a T S b) {U : ℕ} (hU : T ≤ U) :
    out (run init step out a U) = some b := h.iterate.1 U hU

/-- Increasing time and resource bounds preserves initialized runs. -/
theorem Runs.mono {init : Input → State} {a : Input} {U R : ℕ}
    (h : Runs init step out measure a T S b) (hT : T ≤ U) (hS : S ≤ R) :
    Runs init step out measure a U R b := ReachesOutput.mono h hT hS

/-- Initialized runs have unique outputs. -/
theorem Runs.unique {init : Input → State} {a : Input} {U R : ℕ} {c : Output}
    (h : Runs init step out measure a T S b)
    (h' : Runs init step out measure a U R c) : b = c := ReachesOutput.unique h h'

end Cslib.OutputReachability
