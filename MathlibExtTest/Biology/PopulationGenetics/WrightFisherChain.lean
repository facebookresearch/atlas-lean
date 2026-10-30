/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.WrightFisherChain

@[expose] public section

open MeasureTheory Filter Topology MathlibExt.Biology.PopulationGenetics.WrightFisherChain
open MathlibExt.Probability.FiniteMarkovChain

namespace MathlibExtTest.Biology.PopulationGenetics.WrightFisherChain

/-! ### Concrete entries: `M = 2`, one copy of `A` (`Bin(2, 1/2)`) -/

/-- `P(1, 0) = 1/4`. -/
example : (wrightFisher 2).prob 1 0 = 1 / 4 := by
  rw [wrightFisher_prob, coe_z]
  norm_num

/-- `P(1, 1) = 1/2`. -/
example : (wrightFisher 2).prob 1 1 = 1 / 2 := by
  rw [wrightFisher_prob, coe_z]
  norm_num

/-- `P(1, 2) = 1/4`. -/
example : (wrightFisher 2).prob 1 2 = 1 / 4 := by
  rw [wrightFisher_prob, coe_z]
  norm_num

/-- From the absorbing state `0` the chain cannot leave: `P(0, 1) = 0`. -/
example : (wrightFisher 2).prob 0 1 = 0 := by
  rw [wrightFisher_prob, coe_z]
  norm_num

/-- The heterozygosity of the middle state with `M = 2` is `1/2`. -/
example : heterozygosity 2 1 = 1 / 2 := by
  rw [heterozygosity, coe_z]
  norm_num

/-- The fixed states have zero heterozygosity. -/
example : heterozygosity 2 0 = 0 ∧ heterozygosity 2 (Fin.last 2) = 0 := by
  simp [heterozygosity, coe_z]

/-! ### The theorems on instances -/

/-- Rows are probability vectors (the stochastic-matrix field). -/
example (i : Fin 4) : ∑ j, (wrightFisher 3).prob i j = 1 :=
  (wrightFisher 3).row_sum i

/-- The rows are Mathlib's binomial laws. -/
example : (wrightFisher 2).prob 1 1 =
    (ProbabilityTheory.binomial 2 (bernstein.z (1 : Fin 3))).real {1} :=
  wrightFisher_prob_eq_binomial 2 1 1

/-- Martingale: after five generations the expected count from `1` copy (of `3`) is `1`. -/
example : ∑ j, (wrightFisher 3).matPow 5 1 j * ((j : ℕ) : ℝ) = 1 := by
  simpa using sum_matPow_mul_wrightFisher 3 5 1

/-- Absorption at `0` and at `M`. -/
example : (wrightFisher 4).prob 0 0 = 1 ∧ (wrightFisher 4).prob 4 4 = 1 :=
  ⟨wrightFisher_prob_zero_zero 4, wrightFisher_prob_last_last 4⟩

/-- Heterozygosity with `M = 2` halves every generation. -/
example (t : ℕ) : ∑ j, (wrightFisher 2).matPow t 1 j * heterozygosity 2 j =
    (1 / 2) ^ t * (1 / 2) := by
  rw [sum_matPow_mul_heterozygosity]
  congr 2
  · norm_num
  · rw [heterozygosity, coe_z]
    norm_num

/-- Fixation probability `1/2` from one copy out of two. -/
example : Tendsto (fun t => (wrightFisher 2).matPow t 1 (Fin.last 2)) atTop (𝓝 (1 / 2)) := by
  simpa using tendsto_matPow_last (M := 2) (by norm_num) 1

/-- Loss probability `2/3` from one copy out of three. -/
example : Tendsto (fun t => (wrightFisher 3).matPow t 1 0) atTop (𝓝 (2 / 3)) := by
  convert tendsto_matPow_zero (M := 3) (by norm_num) 1 using 2
  norm_num

/-- The middle state of `M = 2` empties out. -/
example : Tendsto (fun t => (wrightFisher 2).matPow t 0 1) atTop (𝓝 0) :=
  tendsto_matPow_interior 0 1 (by decide) (by decide)

/-! ### Boundary case `M = 0` (the one-state chain) -/

/-- With no gene copies the only state is absorbing. -/
example : (wrightFisher 0).prob 0 0 = 1 :=
  wrightFisher_prob_zero_zero 0

/-- With `M = 1` the chain is the identity: the single copy is copied. -/
example : (wrightFisher 1).prob 1 1 = 1 ∧ (wrightFisher 1).prob 1 0 = 0 := by
  refine ⟨wrightFisher_prob_last_last 1, ?_⟩
  rw [wrightFisher_prob, coe_z]
  norm_num

/-! ### Non-vacuity of the path-level hypotheses -/

/-- With `M = 1` the Wright–Fisher matrix is the identity. -/
theorem wrightFisher_one_prob (i j : Fin 2) :
    (wrightFisher 1).prob i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [wrightFisher_prob, coe_z]

/-- The constant process on `Fin 2`: the state never changes. -/
def constChain : ℕ → Fin 2 → Fin 2 := fun _ ω => ω

/-- The constant process (with the full constant filtration) is a Wright–Fisher chain with
`M = 1`: the hypothesis `IsFiniteMarkovChain X (wrightFisher M) ℱ μ` is satisfiable. -/
theorem isFiniteMarkovChain_constChain :
    IsFiniteMarkovChain constChain (wrightFisher 1)
      (Filtration.const ℕ (inferInstance : MeasurableSpace (Fin 2)) le_rfl)
      (Measure.dirac 1) where
  adapted _ := measurable_id
  markov_prop n j := by
    have hf : (fun ω : Fin 2 => if constChain (n + 1) ω = j then (1 : ℝ) else 0) =
        fun ω => (wrightFisher 1).prob (constChain n ω) j := by
      funext ω
      rw [wrightFisher_one_prob]
      rfl
    refine Filter.EventuallyEq.of_eq ?_
    rw [condExp_of_stronglyMeasurable (Filtration.le _ n)
      (by exact measurable_from_top.stronglyMeasurable) Integrable.of_finite]
    exact hf

/-- The constant chain starts at `1` almost surely under `δ₁`. -/
theorem constChain_zero_ae : ∀ᵐ ω ∂(Measure.dirac (1 : Fin 2)), constChain 0 ω = 1 := by
  rw [ae_dirac_iff (Set.toFinite _).measurableSet]
  rfl

/-- On that chain, started at `1` copy out of `1`, fixation has probability `1`. -/
example : (Measure.dirac (1 : Fin 2)).real {ω | ∃ t, constChain t ω = Fin.last 1} = 1 := by
  rw [measureReal_exists_eq_last (by norm_num) isFiniteMarkovChain_constChain
    constChain_zero_ae]
  norm_num

/-- Almost-sure absorption on that chain. -/
example : Measure.dirac (1 : Fin 2)
    {ω | ∃ t, constChain t ω = 0 ∨ constChain t ω = Fin.last 1} = 1 :=
  measure_exists_absorbed isFiniteMarkovChain_constChain constChain_zero_ae

end MathlibExtTest.Biology.PopulationGenetics.WrightFisherChain
