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

-- Apply the probability bound at a positive horizon, starting below the threshold.
example :
    pathMeasure (MeasureTheory.Measure.dirac ())
      (breachSet (fun x (_ : Unit) => x + 1) id 2 0 1) ≤ (1 / 2 : ℝ≥0∞) := by
  simpa using meas_breachSet_le_div (MeasureTheory.Measure.dirac ())
    (f := fun x (_ : Unit) => x + 1) (V := id) (c := 2) (β := 1)
    (measurable_fst.add_const 1) measurable_id (by norm_num) (by norm_num)
    (fun x _ => by simp) 0 1

-- A first hit exactly at the horizon is included; the preceding horizon misses it.
example (ω : ℕ → Unit) :
    ω ∉ breachSet (fun x (_ : Unit) => x + 1) id 2 0 1 ∧
      ω ∈ breachSet (fun x (_ : Unit) => x + 1) id 2 0 2 := by
  constructor
  · simp [breachSet, Nat.le_one_iff_eq_zero_or_eq_one, run]
  · exact ⟨2, le_rfl, by norm_num [run]⟩

#print axioms lintegral_run_succ
#print axioms lintegral_run_le_geom
#print axioms meas_breachSet_le_div

-- Exact drift includes nonzero additive input, not just geometric decay.
example (x₀ : ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, run (fun x (_ : Unit) => 2 * x + 3) x₀ ω n
      ∂pathMeasure (MeasureTheory.Measure.dirac ()) =
        2 ^ n * x₀ + 3 * ∑ k ∈ Finset.range n, (2 : ℝ≥0∞) ^ k := by
  exact lintegral_run_eq_geom (MeasureTheory.Measure.dirac ())
    (f := fun x (_ : Unit) => 2 * x + 3) (V := id) (ρ := 2) (β := 3)
    ((measurable_fst.const_mul 2).add_const 3) measurable_id
    (fun x => by simp) x₀ n

-- The extended-real endpoint is retained; no hidden finiteness premise is needed.
example (n : ℕ) :
    ∫⁻ ω, run (fun x (_ : Unit) => x) (∞ : ℝ≥0∞) ω n
      ∂pathMeasure (MeasureTheory.Measure.dirac ()) = ∞ := by
  simpa using lintegral_run_eq_geom (MeasureTheory.Measure.dirac ())
    (f := fun x (_ : Unit) => x) (V := id) (ρ := 1) (β := 0)
    measurable_fst measurable_id (fun x => by simp) ∞ n

#print axioms lintegral_run_eq_geom
