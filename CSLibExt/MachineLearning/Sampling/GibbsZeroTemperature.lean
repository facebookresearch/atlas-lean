/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.SimulatedAnnealing

/-!
# The zero-temperature Gibbs limit

For a real energy on a finite nonempty state space, the point probabilities of the Gibbs law
converge as temperature tends to zero from above to the uniform probabilities on the global
minimizers. See Levin and Peres, with contributions by Wilmer, *Markov Chains and Mixing Times*,
2nd ed., Example 3.2 (pp. 39–40), with `f = -V` and `λ = exp (1 / T)`.
No proposal kernel enters this limit.
-/

public section

namespace Cslib.MachineLearning.Sampling.SimulatedAnnealing

open Filter Topology MeasureTheory
open scoped ENNReal

/-- As `T → 0⁺`, the Gibbs probability of each state tends to the reciprocal of the number
of global minimizers if the state is a minimizer, and to zero otherwise. -/
theorem tendsto_gibbs_apply {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) (x : S) :
    Tendsto (fun T => gibbs V T x) (𝓝[>] 0)
      (𝓝 ((globalMinSet V).indicator (fun _ => ((globalMinSet V).ncard : ℝ≥0∞)⁻¹) x)) := by
  classical
  have hlim := tendsto_gibbs_globalMinSet V
  by_cases hx : x ∈ globalMinSet V
  · rw [Set.indicator_of_mem hx]
    have hcard : ((globalMinSet V).ncard : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Set.ncard_ne_zero_of_mem hx
    have hmass (T : ℝ) : (gibbs V T).toOuterMeasure (globalMinSet V) =
        (globalMinSet V).ncard * gibbs V T x := by
      let M := (globalMinSet V).toFinite.toFinset
      have hM : (↑M : Set S) = globalMinSet V := Set.Finite.coe_toFinset _
      calc
        (gibbs V T).toOuterMeasure (globalMinSet V) = ∑ y ∈ M, gibbs V T y := by
          rw [← hM, PMF.toOuterMeasure_apply_finset]
        _ = ∑ _y ∈ M, gibbs V T x := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy' : y ∈ globalMinSet V := hM ▸ (Finset.mem_coe.mpr hy)
          have hV : V y = V x := le_antisymm (hy' x) (hx y)
          simp only [gibbs, PMF.ofFintype_apply, Real.softmax, hV]
        _ = (globalMinSet V).ncard * gibbs V T x := by
          rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hM]
    have happly (T : ℝ) : (gibbs V T).toOuterMeasure (globalMinSet V) /
        (globalMinSet V).ncard = gibbs V T x := by
      rw [hmass, mul_comm]
      exact ENNReal.mul_div_cancel_right hcard (ENNReal.natCast_ne_top _)
    have h := ((ENNReal.continuous_div_const _ hcard).tendsto 1).comp hlim
    simpa only [Function.comp_def, happly, one_div] using h
  · rw [Set.indicator_of_notMem hx]
    have hzero : Tendsto (fun T => 1 - (gibbs V T).toOuterMeasure (globalMinSet V))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [Function.comp_def, tsub_self] using
        ((ENNReal.continuous_sub_left ENNReal.one_ne_top).tendsto 1).comp hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
      (fun _ => zero_le) fun T => ?_
    let : MeasurableSpace S := ⊤
    have hm : MeasurableSet (globalMinSet V) := MeasurableSpace.measurableSet_top
    calc
      gibbs V T x = (gibbs V T).toOuterMeasure {x} := (PMF.toOuterMeasure_apply_singleton _ _).symm
      _ ≤ (gibbs V T).toOuterMeasure (globalMinSet V)ᶜ :=
        (gibbs V T).toOuterMeasure.mono (Set.singleton_subset_iff.mpr hx)
      _ = 1 - (gibbs V T).toOuterMeasure (globalMinSet V) := by
        rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm.compl,
          prob_compl_eq_one_sub hm, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]

end Cslib.MachineLearning.Sampling.SimulatedAnnealing
