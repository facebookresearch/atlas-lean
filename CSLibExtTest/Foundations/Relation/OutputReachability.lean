/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Relation.OutputReachability

/-! Certificates for absorbing output reachability and its exact source interface.

The private reference is the source's `Reaches` induction schema, with its state
measure explicit. In particular, `halt` allows an arbitrary remaining budget.
No reference machine or size class is added to the production library.
-/

open Cslib.OutputReachability

namespace Cslib.OutputReachabilityTest

section

variable {State Output Input : Type*}

/-- Exact source induction schema, retained only as a private client reference. -/
private inductive SourceReaches (step : State → State) (out : State → Option Output)
    (measure : State → ℕ) (S : ℕ) (b : Output) : State → ℕ → Prop
  | halt {s : State} {T : ℕ} : out s = some b → measure s ≤ S →
      SourceReaches step out measure S b s T
  | step {s : State} {T : ℕ} : out s = none → measure s ≤ S →
      SourceReaches step out measure S b (step s) T →
        SourceReaches step out measure S b s (T + 1)

variable {step : State → State} {out : State → Option Output}
  {measure : State → ℕ} {s : State} {T S : ℕ} {b : Output}

private theorem source_to_canonical (h : SourceReaches step out measure S b s T) :
    ReachesOutput step out measure s T S b := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho hs _ ih => exact .prepend ho hs ih

private theorem source_of_iteration (ho : out ((next step out)^[T] s) = some b)
    (hs : ∀ n, measure ((next step out)^[n] s) ≤ S) :
    SourceReaches step out measure S b s T := by
  induction T generalizing s with
  | zero => exact .halt ho (hs 0)
  | succ T ih =>
    cases h : out s with
    | some b' =>
      rw [iterate_of_some h, h] at ho
      exact .halt (h.trans ho) (hs 0)
    | none =>
      apply SourceReaches.step h (hs 0)
      apply ih
      · rwa [Function.iterate_succ_apply, next_of_none h] at ho
      · intro n
        have hn := hs (n + 1)
        rwa [Function.iterate_succ_apply, next_of_none h] at hn

private theorem source_iff_canonical :
    SourceReaches step out measure S b s T ↔ ReachesOutput step out measure s T S b := by
  constructor
  · exact source_to_canonical
  · intro h
    exact source_of_iteration (h.iterate.1 T (by omega)) h.iterate.2

private theorem source_iterate (h : SourceReaches step out measure S b s T) :
    (∀ U, T ≤ U → out ((next step out)^[U] s) = some b) ∧
      ∀ n, measure ((next step out)^[n] s) ≤ S :=
  (source_to_canonical h).iterate

private theorem source_iff_iteration : SourceReaches step out measure S b s T ↔
    out ((next step out)^[T] s) = some b ∧
      ∀ n, measure ((next step out)^[n] s) ≤ S :=
  source_iff_canonical.trans reachesOutput_iff_iterate

private theorem source_unique {U R : ℕ} {c : Output}
    (h : SourceReaches step out measure S b s T)
    (h' : SourceReaches step out measure R c s U) : b = c :=
  (source_to_canonical h).unique (source_to_canonical h')

/-- The source `Runs` specialization uses the same initial state and argument order. -/
private def SourceRuns (init : Input → State) (step : State → State)
    (out : State → Option Output) (measure : State → ℕ)
    (a : Input) (T S : ℕ) (b : Output) : Prop :=
  SourceReaches step out measure S b (init a) T

private theorem source_runs_iff {init : Input → State} {a : Input} :
    SourceRuns init step out measure a T S b ↔ Runs init step out measure a T S b :=
  source_iff_canonical

private theorem source_runs_iff_iteration {init : Input → State} {a : Input} :
    SourceRuns init step out measure a T S b ↔
      out (run init step out a T) = some b ∧
        ∀ n, measure (run init step out a n) ≤ S :=
  source_runs_iff.trans runs_iff_iterate

private def counterStep (n : ℕ) : ℕ := n + 1

private def counterOut (n : ℕ) : Option ℕ := if 3 ≤ n then some n else none

private theorem reaches_three : ReachesOutput counterStep counterOut id 0 3 3 3 := by
  apply ReachesOutput.prepend (by decide) (by decide)
  apply ReachesOutput.prepend (by decide) (by decide)
  apply ReachesOutput.prepend (by decide) (by decide)
  exact ReachesOutput.halt (by decide) (by decide)

example : counterOut ((next counterStep counterOut)^[7] 0) = some 3 :=
  reaches_three.iterate.1 7 (by decide)

example : ReachesOutput counterStep counterOut id 0 3 3 3 := by
  apply reachesOutput_iff_bounded_iterate.mpr
  refine ⟨rfl, fun n hn => ?_⟩
  have he : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl <;> decide

example : counterStep 3 = 4 := rfl

example : (next counterStep counterOut)^[7] 0 = 3 := rfl

example : ¬ReachesOutput counterStep counterOut id 0 2 3 3 := by
  intro h
  have ho := h.iterate.1 2 (by decide)
  change (none : Option ℕ) = some 3 at ho
  cases ho

example : ¬ReachesOutput counterStep counterOut id 0 3 2 3 := by
  intro h
  have hs := h.iterate.2 3
  change 3 ≤ 2 at hs
  omega

example (T S : ℕ) : ¬ReachesOutput counterStep counterOut id 0 T S 4 := by
  intro h
  have he := reaches_three.unique h
  omega

example (T : ℕ) : ReachesOutput counterStep counterOut id 3 T 3 3 :=
  .halt (by decide) (by decide)

example : ReachesOutput counterStep counterOut id 3 0 3 3 :=
  .halt (by decide) (by decide)

example (T S b : ℕ) : ¬ReachesOutput id (fun _ : ℕ => none) (fun _ => 0) 0 T S b := by
  intro h
  have ho := h.iterate.1 T (by omega)
  change (none : Option ℕ) = some b at ho
  cases ho

example : SourceReaches counterStep counterOut id 3 3 0 3 :=
  source_iff_canonical.mpr reaches_three

example (T : ℕ) : SourceReaches counterStep counterOut id 3 3 3 T :=
  .halt (by decide) (by decide)

example : SourceRuns (fun _ : Unit => 0) counterStep counterOut id () 3 3 3 :=
  source_runs_iff.mpr reaches_three

example : Runs (fun _ : Unit => 0) counterStep counterOut id () 3 3 3 := reaches_three

example : counterOut (run (fun _ : Unit => 0) counterStep counterOut () 7) = some 3 :=
  Runs.out_run reaches_three (by decide)

example : Runs (fun _ : Unit => 0) counterStep counterOut id () 7 9 3 :=
  Runs.mono reaches_three (by decide) (by decide)

example (T S : ℕ) (b : ℕ)
    (h : Runs (fun _ : Unit => 0) counterStep counterOut id () T S b) : b = 3 :=
  Runs.unique h reaches_three

end

end Cslib.OutputReachabilityTest
