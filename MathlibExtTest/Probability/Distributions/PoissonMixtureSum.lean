/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonMixtureSum
import MathlibExt.Probability.Distributions.Gamma
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-! Tests for sums of independent mixed Poisson counts.

* non-vacuity: independent gamma rates satisfy the hypotheses;
* the zero class of the total is the product of the zero classes;
* two summands with total `1`: `P(N₁ + N₂ = 1) = p₁(1) p₂(0) + p₁(0) p₂(1)`;
* with no summands the total is `0`, so it never equals `1`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Probability.Distributions.PoissonMixtureSum

/-- Non-vacuity: gamma laws with positive shapes and rates are finite measures on `[0, ∞)`, so
the theorem applies to independent gamma rates. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (k : ℕ) :
    poissonMixtureReal ((Measure.pi fun i => gammaMeasure (a i) (b i)).map fun x => ∑ i, x i) k =
      ∑ j ∈ univ.piAntidiag k, ∏ i, poissonMixtureReal (gammaMeasure (a i) (b i)) (j i) := by
  have : ∀ i, IsProbabilityMeasure (gammaMeasure (a i) (b i)) := fun i =>
    isProbabilityMeasure_gammaMeasure (ha i) (hb i)
  exact poissonMixtureReal_pi_map_sum (fun i => ae_nonneg_gammaMeasure _ _) k

/-- The zero class of the total is the product of the zero classes: `P(∑ᵢ Nᵢ = 0) = ∏ᵢ P(Nᵢ = 0)`,
as `j = 0` is the only split of `0`. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : ι → Measure ℝ} [∀ i, IsFiniteMeasure (ν i)]
    (h0 : ∀ i, ∀ᵐ r ∂ν i, 0 ≤ r) :
    poissonMixtureReal ((Measure.pi ν).map fun x => ∑ i, x i) 0 =
      ∏ i, poissonMixtureReal (ν i) 0 := by
  rw [poissonMixtureReal_pi_map_sum h0, piAntidiag_zero, sum_singleton]
  rfl

/-- Two summands with total `1`: `P(N₀ + N₁ = 1) = p₀(0) p₁(1) + p₀(1) p₁(0)`. -/
example {ν : Fin 2 → Measure ℝ} [∀ i, IsFiniteMeasure (ν i)] (h0 : ∀ i, ∀ᵐ r ∂ν i, 0 ≤ r) :
    poissonMixtureReal ((Measure.pi ν).map fun x => ∑ i, x i) 1 =
      poissonMixtureReal (ν 0) 0 * poissonMixtureReal (ν 1) 1 +
        poissonMixtureReal (ν 0) 1 * poissonMixtureReal (ν 1) 0 := by
  rw [poissonMixtureReal_pi_map_sum h0, piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple_two, sum_map]
  simp [Fin.prod_univ_two, Finset.Nat.antidiagonal_succ]

/-- With no summands the total count is `0`: it is never `1`. -/
example {ν : Fin 0 → Measure ℝ} :
    poissonMixtureReal ((Measure.pi ν).map fun x => ∑ i, x i) 1 = 0 := by
  have : ∀ i, IsFiniteMeasure (ν i) := fun i => i.elim0
  rw [poissonMixtureReal_pi_map_sum fun i => i.elim0]
  simp

end MathlibExtTest.Probability.Distributions.PoissonMixtureSum
