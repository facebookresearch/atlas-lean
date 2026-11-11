/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonKernel

/-!
# Tests for Poisson moments, finite additivity, and Poisson kernels
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.Distributions.PoissonKernel

/-- `Po(3)` has mean `3`. -/
example : ∫ n, (n : ℝ) ∂poissonMeasure 3 = 3 := by
  simpa using integral_natCast_poissonMeasure 3

/-- `Po(2)` has second moment `2 + 2² = 6`. -/
example : ∫ n, (n : ℝ) ^ 2 ∂poissonMeasure 2 = 6 := by
  rw [integral_natCast_sq_poissonMeasure]
  norm_num

/-- `Po(2)` has variance `2`. -/
example : Var[fun n : ℕ => (n : ℝ); poissonMeasure 2] = 2 := by
  simpa using variance_natCast_poissonMeasure 2

/-- Boundary: `Po(0)` is the point mass at `0`, with mean and variance `0`. -/
example : poissonMeasure 0 = Measure.dirac 0 ∧ ∫ n, (n : ℝ) ∂poissonMeasure 0 = 0 ∧
    Var[fun n : ℕ => (n : ℝ); poissonMeasure 0] = 0 := by
  refine ⟨poissonMeasure_zero, ?_, ?_⟩
  · simpa using integral_natCast_poissonMeasure 0
  · simpa using variance_natCast_poissonMeasure 0

/-- Two independent counts `Po(1)` and `Po(2)` sum to `Po(3)`. -/
example : (Measure.pi fun i : Fin 2 => poissonMeasure (![1, 2] i)).map
    (fun N : Fin 2 → ℕ => ∑ i, N i) = poissonMeasure 3 := by
  rw [map_sum_pi_poissonMeasure]
  congr 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num

/-- One count: the sum over a singleton index is the count itself. -/
example (r : ℝ≥0) : (Measure.pi fun _ : Unit => poissonMeasure r).map
    (fun N : Unit → ℕ => ∑ i, N i) = poissonMeasure r := by
  simpa using map_sum_pi_poissonMeasure (fun _ : Unit => r)

/-- The kernels evaluate to the Poisson laws. -/
example (r : ℝ≥0) (s : Fin 3 → ℝ≥0) : poissonMeasureKernel r = poissonMeasure r ∧
    piPoissonKernel (Fin 3) s = Measure.pi fun i => poissonMeasure (s i) :=
  ⟨rfl, rfl⟩

/-- The kernels are Markov. -/
example : IsMarkovKernel poissonMeasureKernel ∧ IsMarkovKernel (piPoissonKernel (Fin 3)) :=
  ⟨inferInstance, inferInstance⟩

/-- Summing a product of Poisson kernels gives the Poisson kernel at the summed mean. -/
example (s : Fin 3 → ℝ≥0) :
    (piPoissonKernel (Fin 3)).map (fun N : Fin 3 → ℕ => ∑ i, N i) s =
      poissonMeasure (∑ i, s i) := by
  rw [piPoissonKernel_map_sum]
  rfl

/-- Finite additivity with an empty index set gives the point mass at `0`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin 3 → Ω → ℕ} {r : Fin 3 → ℝ≥0} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) :
    HasLaw (∑ i ∈ ∅, X i) (Measure.dirac 0) P := by
  simpa [poissonMeasure_zero] using iIndepFun.hasLaw_sum_poissonMeasure hind hX ∅

end MathlibExtTest.Probability.Distributions.PoissonKernel
