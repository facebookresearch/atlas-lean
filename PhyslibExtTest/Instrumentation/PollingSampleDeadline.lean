/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.PollingSampleDeadline
import Mathlib.Tactic.NormNum

@[expose] public section

open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol
open Cslib.Semantics.Peripheral.PollDriverSimulation
open Cslib.Semantics.Peripheral.ProducerInterruptSimulation
open PhyslibExt.Instrumentation.PollingSampleDeadline

namespace PhyslibExtTest.Instrumentation.PollingSampleDeadline

/-! ### Worst phase -/

/-- In the worst-phase run with samples `7` (ID 0) and `9` (ID 1), publication `0` completes in
the same cycle as the empty Ready check before it, at cycle `1`; the second publication completes
at cycle `10`. -/
example :
    cycleAt (worstPhaseTrace 7 9) 0 = 1 ∧ cycleAt (worstPhaseTrace 7 9) 1 = 1 ∧
      cycleAt (worstPhaseTrace 7 9) 10 = 10 ∧
      publicationAt (worstPhaseTrace 7 9) 10 = some (1, 9) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The headline applied to the worst-phase run at `fclk = 1`, `Tmin = 8`, `Cpoll = 3`,
`Cread = 2`, `Cirq = 1`, `Cbus = 1`: the driver's returned IDs are the publication IDs. -/
example : driverReadIds (labels (worstPhaseTrace 7 9)) =
    publicationIds (labels (worstPhaseTrace 7 9)) := by
  obtain ⟨hrun, -, -, -, hgap, hresp, hbudget, hsole, -, -⟩ := worstPhase_valid 7 9
  exact ((pollingSampleDeadline_correct stallHandler rely_stallHandler () _ _ hrun 1 8 one_pos
    (by norm_num) 3 2 1 1 hgap hresp hbudget (fun n => (n : ℝ))).2.2 hsole).2.1

/-- The headline's first clause on the worst-phase run: publication `(0, 7)` at step `1` is read
as `some (0, 7)` before the publication at step `10`, within `7 / 1` seconds. -/
example : ∃ r, 1 < r ∧ ((labels (worstPhaseTrace 7 9))[r]?).bind readResult? = some (some (0, 7)) ∧
    timeAt 1 (worstPhaseTrace 7 9) r - timeAt 1 (worstPhaseTrace 7 9) 1 ≤
      ((3 + 2 + 1 + 1 : ℕ) : ℝ) / 1 ∧ r < 10 := by
  obtain ⟨hrun, -, hpub, -, hgap, hresp, hbudget, -, -, -⟩ := worstPhase_valid 7 9
  obtain ⟨r, h1r, hr, hle, -, hlater⟩ := (pollingSampleDeadline_correct stallHandler
    rely_stallHandler () _ _ hrun 1 8 one_pos (by norm_num) 3 2 1 1 hgap hresp hbudget
    (fun n => (n : ℝ))).1 1 0 7 hpub
  exact ⟨r, h1r, hr, hle, hlater 10 (by omega) rfl⟩

/-! ### Necessity of the strict budget and of the interrupt bound -/

/-- With the budget equal to the gap (`7 / 1 = 7`), a run meeting the gap and response premises
with a sole reader loses publication `0`. -/
example : (0 : ℕ) ∈ publicationIds (labels (boundaryTrace 7 9)) ∧
    (0 : ℕ) ∉ driverReadIds (labels (boundaryTrace 7 9)) ∧
    PublicationGap 1 7 (boundaryTrace 7 9) ∧ ((3 + 2 + 1 + 1 : ℕ) : ℝ) / 1 = 7 := by
  obtain ⟨-, hgap, -, -, heq, -, -, hpub, hdrv⟩ := budget_not_strict_loses 7 9
  refine ⟨by rw [hpub]; simp, by rw [hdrv]; simp, hgap, heq⟩

/-- With an interrupt stall of `3` cycles against `Cirq = 1`, the response premise fails at
publication `0`, holds there with `Cirq = 3`, and publication `0` is lost even though the gap and
the strict budget hold. -/
example : ¬ RespondsWithin 3 2 1 1 (delayedInterruptTrace 7 9) 1 ∧
    RespondsWithin 3 2 3 1 (delayedInterruptTrace 7 9) 1 ∧
    PublicationGap 1 8 (delayedInterruptTrace 7 9) ∧
    (0 : ℕ) ∈ publicationIds (labels (delayedInterruptTrace 7 9)) ∧
    (0 : ℕ) ∉ driverReadIds (labels (delayedInterruptTrace 7 9)) := by
  obtain ⟨-, hgap, -, -, hirq3, hnot, -, hpub, hdrv⟩ := delayedInterrupt_loses 7 9
  exact ⟨hnot, hirq3, hgap, by rw [hpub]; simp, by rw [hdrv]; simp⟩

/-! ### Necessity of the sole-reader hypothesis -/

/-- Another reader takes publication `(0, 7)` one cycle after it is published, and the driver's
Ready check then sees an empty slot. Charges per step: `0 1 1`. -/
def stolenReadTrace : CostedTrace ℕ :=
  [⟨.driver (.visible (.env (.publish 0 7))), 0⟩,
    ⟨.driver (.visible (.env (.read (some (0, 7))))), 1⟩,
    ⟨.driver (.visible (.poll false)), 1⟩]

/-- The stolen-read run meets every timing premise at `fclk = 1`, `Tmin = 8` with budget `7`,
and publication `0` is read by the other reader, but the driver returns no ID while one sample
was published: `NoOtherReader` fails and the driver-side clause fails with it. -/
example :
    (systemLTS (stallHandler (α := ℕ))).MTr (initialSystem ()) (labels stolenReadTrace)
        ⟨(), ⟨.branchReady, false, none, none⟩, none⟩ ∧
      PublicationGap 1 8 stolenReadTrace ∧
      (∀ i, (publicationAt stolenReadTrace i).isSome → RespondsWithin 3 2 1 1 stolenReadTrace i) ∧
      ((labels stolenReadTrace)[1]?).bind readResult? = some (some (0, 7)) ∧
      ¬ NoOtherReader (labels stolenReadTrace) ∧
      driverReadIds (labels stolenReadTrace) = [] ∧
      publicationIds (labels stolenReadTrace) = [0] := by
  have hpub : ∀ i, (publicationAt stolenReadTrace i).isSome → i = 0 := by
    intro i h
    rcases i with _ | _ | _ | i
    · rfl
    all_goals simp [publicationAt, labels, stolenReadTrace, publication?] at h
  refine ⟨?_, ?_, ?_, rfl, fun h => h 1 (some (0, 7)) rfl, rfl, rfl⟩
  · exact
      .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 0 7))) <|
      .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.read _))) <|
      .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) .refl
  · intro i j hij hi hj
    have := hpub i hi
    have := hpub j hj
    omega
  · intro i hi
    obtain rfl := hpub i hi
    refine ⟨2, by omega, ⟨false, rfl⟩, 0, 0, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, stolenReadTrace, isInterruptStep]
    · simp [interruptCycles, stolenReadTrace, isInterruptStep]
    · intro h2
      simp [labels, stolenReadTrace] at h2

end PhyslibExtTest.Instrumentation.PollingSampleDeadline
