/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.EnergyBased.Hopfield
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Boundary checks for the asynchronous Hopfield interface -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace Cslib.MachineLearning.Hopfield

example (v : Fin 0 → Bool) : Stable 0 0 v ∧ energy 0 v = 0 := by
  simp [Stable, energy]

example : ¬ Nonempty (ℕ → Fin 0) := by
  rintro ⟨σ⟩
  exact Fin.elim0 (σ 0)

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ¬ Nonempty (ℕ → Ω → Fin 0) := by
  rintro ⟨σ⟩
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
  exact Fin.elim0 (σ 0 ω)

example {N : ℕ} (T : Fin N → Fin N → ℝ) (U : Fin N → ℝ)
    (v : Fin N → Bool) (i : Fin N) (h : localField T v i = U i) :
    step T U i v = v := by
  simp [step, h]

example (v : Fin 1 → Bool) :
    localField (fun _ _ => -1) v 0 = 0 ∧
    step (fun _ _ => -1) 0 0 v = v ∧ energy (fun _ _ => -1) v = 0 := by
  simp [localField, step, energy]

private noncomputable def pairWeights : Fin 2 → Fin 2 → ℝ :=
  !![0, 1; 1, 0]

private def unfairStart : Fin 2 → Bool := ![true, false]

private theorem unfair_stutters : step pairWeights 0 0 unfairStart = unfairStart := by
  simp [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ, pairWeights,
    unfairStart]

example : Matrix.IsSymm pairWeights := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

example : ¬ Fair (fun _ => (0 : Fin 2)) := by
  intro h
  obtain ⟨k, _, hk⟩ := h 1 0
  exact (by decide : (0 : Fin 2) ≠ 1) hk

example (k : ℕ) : trajectory pairWeights 0 (fun _ => 0) unfairStart k = unfairStart := by
  induction k with
  | zero => rfl
  | succ k ih => rw [trajectory_succ, ih, unfair_stutters]

example : ¬ Stable pairWeights 0 unfairStart := by
  intro h
  have h₁ := congrFun (h 1) 1
  norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
    pairWeights, unfairStart] at h₁

private noncomputable def traceWeights : Fin 3 → Fin 3 → ℝ :=
  !![0, 1, -1; 1, 0, 1; -1, 1, 0]

private def roundRobin (k : ℕ) : Fin 3 := ⟨k % 3, Nat.mod_lt k (by decide)⟩

private noncomputable def trace : ℕ → Fin 3 → Bool :=
  trajectory traceWeights 0 roundRobin ![true, false, true]

example : Matrix.IsSymm traceWeights := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

example : Fair roundRobin := by
  intro i K
  refine ⟨K * 3 + i.val, by omega, Fin.ext ?_⟩
  change (K * 3 + i.val) % 3 = i.val
  have := i.isLt
  omega

private theorem trace_one : trace 1 = ![false, false, true] := by
  have hs : roundRobin 0 = 0 := rfl
  rw [trace, trajectory_succ, trajectory_zero, hs]
  funext j
  fin_cases j <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      traceWeights, Function.update]

private theorem trace_two : trace 2 = ![false, true, true] := by
  have hs : roundRobin 1 = 1 := rfl
  have ht := trace_one
  rw [trace] at ht ⊢
  rw [trajectory_succ, ht, hs]
  funext j
  fin_cases j <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      traceWeights, Function.update]

example : trace 1 ≠ trace 0 ∧ trace 2 ≠ trace 1 := by
  rw [trace_one, trace_two]
  constructor
  · intro h
    exact Bool.noConfusion (congrFun h 0)
  · intro h
    exact Bool.noConfusion (congrFun h 1)

example : Stable traceWeights 0 (trace 2) := by
  rw [trace_two]
  intro i
  fin_cases i <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      traceWeights, ← Function.update_eq_self]

example : energy traceWeights (trace 0) = 1 ∧
    energy traceWeights (trace 1) = 0 ∧ energy traceWeights (trace 2) = -1 := by
  rw [trace_one, trace_two, trace, trajectory_zero]
  norm_num [energy, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ, traceWeights]

private noncomputable def uniformNeuron : Measure (Fin 2) :=
  Measure.uniformOfFinset univ

private instance : IsProbabilityMeasure uniformNeuron where
  measure_univ := by
    rw [uniformNeuron, Measure.uniformOfFinset_apply]
    simp [ENNReal.div_self]

example : IIDFullSupport (Measure.infinitePi (fun _ : ℕ => uniformNeuron))
    (fun k (ω : ℕ → Fin 2) => ω k) := by
  refine ⟨measurable_pi_apply, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (fun _ => measurable_id)
  · intro k
    exact ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      (Measure.infinitePi_map_eval _ k).trans
        (Measure.infinitePi_map_eval (fun _ : ℕ => uniformNeuron) 0).symm⟩
  · intro i
    change 0 < Measure.infinitePi _ ((fun ω : ℕ → Fin 2 => ω 0) ⁻¹' {i})
    rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton i),
      Measure.infinitePi_map_eval]
    simp [uniformNeuron]

end Cslib.MachineLearning.Hopfield
