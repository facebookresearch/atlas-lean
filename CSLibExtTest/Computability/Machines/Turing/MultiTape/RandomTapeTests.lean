/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Machines.Turing.MultiTape.RandomTape
import Mathlib.Probability.Independence.InfinitePi

/-! # One-step machines and rereading a cell of the random tape -/

open Turing Cslib.Turing Cslib.Turing.RandomTapeTM MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CSLibExtTest.RandomTapeTM

-- One transition: look at the random cell, optionally emit a bit, and halt.
private def single (emit : Option Bool → Option Bool) : RandomTapeTM 0 1 where
  start := 0
  transition _ _ w := ⟨0, fun _ ↦ (none, 0), emit (w 0), none⟩
  readOnly _ _ _ := rfl

private theorem single_time (emit) : (single emit).RunsInTime (fun _ ↦ 1) := by
  intro x r
  rw [run_eq_iterate]; rfl

private theorem single_ppt (emit) : (single emit).IsPPT := by
  exact ⟨1, by simpa [RunsInTime] using single_time emit⟩

private theorem single_output (emit) (x : List Bool) (r : ℤ → Bool) :
    ((single emit).run x r 1).output = (emit (some (r 0))).toList := by
  rw [run_eq_iterate]
  simp [single, Cslib.Turing.MultiTapeTM.stepWith, Cfg.workTapeSymbols, loadTape]

-- The empty word also takes one transition: it cannot satisfy a zero deadline there.
example (emit) {T : ℕ → ℕ} (h : T 0 = 0) : ¬ (single emit).RunsInTime T := by
  intro ht
  have hh := ht [] (fun _ ↦ false)
  simp only [List.length_nil, h, run_eq_iterate] at hh
  change some (0 : Fin 1) = none at hh
  cases hh

-- A deterministic machine ignores the tape. Its unique output has full mass.
example (x : List Bool) : (single (fun _ ↦ some true)).outputLaw (single_ppt _) x [true] = 1 := by
  rw [outputLaw_apply _ _ (single_time _)]
  simp [single_output]

-- A genuinely random machine: either one-letter word has mass exactly one half, on any input.
example (x : List Bool) (b : Bool) : (single id).outputLaw (single_ppt id) x [b] = (2 : ℝ≥0∞)⁻¹ := by
  rw [outputLaw_apply _ _ (single_time _)]
  have he : {r : ℤ → Bool | ((single id).run x r 1).output = [b]} =
      (fun r : ℤ → Bool ↦ r 0) ⁻¹' {b} := by ext; simp [single_output]
  rw [he, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton b), tapeLaw,
    Measure.infinitePi_map_eval]
  cases b <;> simp <;> norm_num [unitInterval.toNNReal, unitInterval.symm] <;>
    change ((1 / 2 : ℝ≥0) : ℝ≥0∞) = _ <;> norm_num

-- Independence is indexed by cells, not by the times at which they are read.
example : iIndepFun (fun i : ℤ ↦ fun r : ℤ → Bool ↦ r i) tapeLaw :=
  iIndepFun_infinitePi (X := fun _ b ↦ b) (fun _ ↦ measurable_id)

-- Move right, then left, then halt. Each transition copies the current random bit to output.
private def reread : RandomTapeTM 0 3 where
  start := 0
  transition q _ w := ⟨0, fun _ ↦ (none, if q = 0 then 1 else -1), w 0,
    if q = 0 then some 1 else if q = 1 then some 2 else none⟩
  readOnly _ _ _ := rfl

example (x : List Bool) (r : ℤ → Bool) :
    (reread.run x r 3).output = [r 0, r 1, r 0] := by
  rw [run_eq_iterate]
  simp [Function.iterate_succ_apply, Cslib.Turing.MultiTapeTM.stepWith, reread, Cfg.workTapeSymbols,
    loadTape, Action.apply]

end CSLibExtTest.RandomTapeTM
