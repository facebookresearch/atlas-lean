/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Probability.Process.IteratedRandomMap

open ProbabilityTheory.IteratedRandomMap
open scoped ENNReal

-- A breach at the initial state is counted even when the horizon is zero.
example {S D : Type*} (f : S → D → S) (V : S → ℝ≥0∞)
    (c : ℝ≥0∞) (x : S) (ω : ℕ → D) :
    ω ∈ breachSet f V c x 0 ↔ c ≤ V x := by
  simp [breachSet]

-- A chain freezes at its first hit, including a hit at time zero.
example {S D : Type*} (f : S → D → S) (V : S → ℝ≥0∞)
    (c : ℝ≥0∞) (x : S) (ω : ℕ → D) (h : c ≤ V x) (n : ℕ) :
    run (stopped f V c) x ω n = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, stopped_of_le h]

-- A deterministic halving chain realizes the geometric drift bound with zero slack.
example (x₀ : ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, run (fun x (_ : Unit) => x / 2) x₀ ω n
      ∂pathMeasure (MeasureTheory.Measure.dirac ()) ≤ (1 / 2 : ℝ≥0∞) ^ n * x₀ := by
  simpa using lintegral_run_le_geom (MeasureTheory.Measure.dirac ())
    (f := fun x (_ : Unit) => x / 2) (V := id) (ρ := 1 / 2) (β := 0)
    (measurable_fst.div_const 2) measurable_id
    (fun x => by simp [div_eq_mul_inv, mul_comm]) x₀ n

#print axioms lintegral_run_succ
#print axioms lintegral_run_le_geom
#print axioms meas_breachSet_le_div
