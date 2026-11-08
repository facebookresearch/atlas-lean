/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvergenceInProbability

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MathlibExt.Probability.ConvergenceInProbability

namespace MathlibExtTest.Probability.ConvergenceInProbability

/-- A constant sequence converges in probability to its constant value:
the bad sets `{ω | ε < |c - c|}` are empty. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => μ {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|})
        atTop (𝓝 0) := by
  intro ε hε
  have hset : ∀ n : ℕ, {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|} = ∅ := by
    intro n
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    simp only [sub_self, abs_zero, not_lt]
    exact hε.le
  have h0 : ∀ n : ℕ, μ {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|} = 0 :=
    fun n => by rw [hset n, measure_empty]
  have hev : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[atTop]
      (fun n : ℕ => μ {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|}) :=
    Filter.Eventually.of_forall fun n => (h0 n).symm
  exact tendsto_const_nhds.congr' hev

/-- The constant-sequence case of the main theorem: every subsequence of a
constant sequence has a further subsequence converging a.e. to the constant. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : ℝ) :
    ∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => (fun (_ : ℕ) (_ : Ω) => c) (ns (ns' k)) ω)
          atTop (𝓝 ((fun (_ : Ω) => c) ω)) := by
  have hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => μ {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|})
        atTop (𝓝 0) := by
    intro ε hε
    have hset : ∀ n : ℕ,
        {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|} = ∅ := by
      intro n
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      simp only [sub_self, abs_zero, not_lt]
      exact hε.le
    have h0 : ∀ n : ℕ, μ {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|} = 0 :=
      fun n => by rw [hset n, measure_empty]
    have hev : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[atTop]
        (fun n : ℕ => μ {ω : Ω | ε < |(fun (_ : ℕ) (_ : Ω) => c) n ω - (fun (_ : Ω) => c) ω|}) :=
      Filter.Eventually.of_forall fun n => (h0 n).symm
    exact tendsto_const_nhds.congr' hev
  exact (convergence_in_probability_iff_subsequential_ae_convergence
    (X := fun _ _ => c) (Y := fun _ => c)
    (fun _ => aestronglyMeasurable_const)).mp hprob

/-- The scaled constants `1 / (n + 1)` converge in probability to `0`:
for fixed `ε > 0` the bad set is eventually empty. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => μ {_ω : Ω | ε < |(1 : ℝ) / ((n : ℝ) + 1) - 0|})
        atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  have hev : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[atTop]
      (fun n : ℕ => μ {_ω : Ω | ε < |(1 : ℝ) / ((n : ℝ) + 1) - 0|}) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      calc (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
            apply one_div_le_one_div_of_le
            · positivity
            · have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
              linarith
        _ < ε := hN
    have hset : {_ω : Ω | ε < |(1 : ℝ) / ((n : ℝ) + 1) - 0|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [sub_zero, abs_of_nonneg (by positivity)]
      exact not_lt.mpr hlt.le
    rw [hset, measure_empty]
  exact tendsto_const_nhds.congr' hev

/-- The reverse direction of the main theorem: the subsequential a.e.
hypothesis implies convergence in probability. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hsub : ∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => X (ns (ns' k)) ω) atTop (𝓝 (Y ω))) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0) :=
  (convergence_in_probability_iff_subsequential_ae_convergence hX).mpr hsub

#print axioms MathlibExt.Probability.ConvergenceInProbability.tendstoInMeasure_iff_tendsto_measure_abs_sub
#print axioms MathlibExt.Probability.ConvergenceInProbability.convergence_in_probability_iff_subsequential_ae_convergence

end MathlibExtTest.Probability.ConvergenceInProbability
