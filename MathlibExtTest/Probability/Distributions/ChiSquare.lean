/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ChiSquare

/-!
# Tests for chi-square laws: no atoms

* `χ²₁` puts no mass at `0` (`chiSquareMeasure_singleton`), the fact that separates it from the
  degenerate limit `δ₀` in the monomorphic Hardy–Weinberg and zero-cell Pearson counterexamples.
* The `NullSingletonClass` instance: every countable set is `χ²_p`-null.
* Non-vacuity: `χ²₁` is a probability measure, so it is not the zero measure, yet each point,
  and the countable set `ℕ ⊆ ℝ`, is null; consequently `χ²₁ ≠ δ₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace ChiSquareTest

/-- `χ²₁` has no atom at `0`. -/
example : chiSquareMeasure 1 {0} = 0 := chiSquareMeasure_singleton 1 0

/-- Through the instance, Mathlib's generic `measure_singleton` applies to every `χ²_p`. -/
example (p : ℕ) (x : ℝ) : chiSquareMeasure p {x} = 0 := measure_singleton x

/-- Every countable set is `χ²_p`-null; e.g. the natural numbers inside `ℝ`. -/
example (p : ℕ) : chiSquareMeasure p (Set.range ((↑) : ℕ → ℝ)) = 0 :=
  (Set.countable_range _).measure_zero _

/-- Non-vacuity: `χ²₁` has total mass `1`, so the atom statement is not about the zero
measure. -/
example : chiSquareMeasure 1 Set.univ = 1 := by
  have := isProbabilityMeasure_chiSquareMeasure one_pos
  exact measure_univ

/-- **`χ²₁` is not the point mass at `0`**: the Dirac mass gives `{0}` mass `1`, `χ²₁` gives it
mass `0`. -/
example : chiSquareMeasure 1 ≠ Measure.dirac 0 := by
  intro h
  have := chiSquareMeasure_singleton 1 0
  rw [h, Measure.dirac_apply_of_mem (Set.mem_singleton 0)] at this
  exact one_ne_zero this

/-- Chi-square with one degree is a probability law. -/
example : IsProbabilityMeasure (chiSquareMeasure 1) :=
  isProbabilityMeasure_chiSquareMeasure (by norm_num)

/-- Chi-square MGF at zero is one. -/
example : mgf id (chiSquareMeasure 2) 0 = 1 := by
  rw [mgf_chiSquareMeasure_of_lt (by norm_num) (by norm_num)]
  norm_num

/-- The chi-square-one MGF matches the Gaussian-square MGF at zero. -/
example : mgf id (gammaMeasure (1 / 2) (1 / 2)) 0
    = (Real.sqrt (1 - 2 * (0 : ℝ)))⁻¹ :=
  mgf_gammaMeasure_half_half_eq_sqrt (by norm_num)

/-- Two chi-square-one MGFs multiply to chi-square-two below `1/2`. -/
example (t : ℝ) (ht : t < 1 / 2) :
    mgf id (chiSquareMeasure 1) t * mgf id (chiSquareMeasure 1) t
      = mgf id (chiSquareMeasure 2) t := by
  have h := prod_mgf_chiSquareMeasure_eq_mgf_sum
    (s := ({0, 1} : Finset ℕ)) (p := fun _ => 1) (by simp) (fun _ _ => by norm_num) ht
  have hsum : ∑ _i ∈ ({0, 1} : Finset ℕ), (1 : ℕ) = 2 := by
    rw [Finset.sum_pair (by norm_num)]
  have hprod : ∏ _i ∈ ({0, 1} : Finset ℕ), mgf id (chiSquareMeasure 1) t
      = mgf id (chiSquareMeasure 1) t * mgf id (chiSquareMeasure 1) t := by
    rw [Finset.prod_pair (by norm_num)]
  rw [hprod, hsum] at h
  exact h

/-- Finite-family API: MGFs multiply over `Finset.univ` for `Fin 2`. -/
example (t : ℝ) (ht : t < 1 / 2) :
    ∏ i ∈ (Finset.univ : Finset (Fin 2)),
        mgf id (chiSquareMeasure ((fun _ : Fin 2 => 1) i)) t
      = mgf id (chiSquareMeasure
        (∑ i ∈ (Finset.univ : Finset (Fin 2)), (fun _ : Fin 2 => 1) i)) t :=
  prod_mgf_chiSquareMeasure_eq_mgf_sum Finset.univ_nonempty
    (fun _ _ => by norm_num) ht

end ChiSquareTest
