/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Multinomial

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MathlibExtTest.Probability.Distributions.Multinomial

/-- A concrete mass: two throws into three cells with `p = (1/2, 1/4, 1/4)` land once in each
of the first two cells with probability `2! / (1! 1! 0!) · (1/2) (1/4) = 1/4`. -/
example : multinomialReal 2 ![(1 / 2 : ℝ), 1 / 4, 1 / 4] ![1, 1, 0] = 1 / 4 := by
  rw [multinomialReal_eq_factorial_div (by simp [Fin.sum_univ_three])]
  simp [Fin.prod_univ_three]

/-- Boundary: off the simplex `∑ᵢ xᵢ = N` the mass is `0`. -/
example : multinomialReal 2 ![(1 / 2 : ℝ), 1 / 4, 1 / 4] ![1, 1, 1] = 0 :=
  multinomialReal_of_sum_ne (by simp [Fin.sum_univ_three])

/-- Boundary: `N = 0` puts all mass on the zero vector. -/
example (p : Fin 3 → ℝ) : multinomialReal 0 p 0 = 1 := by
  simp [multinomialReal, Nat.multinomial]

/-- Outside the parameter domain the total mass is `(∑ᵢ pᵢ) ^ N`, not `1`: with `p = (1, 1)` and
`N = 3` it is `8` (the formula is a polynomial in `p`). -/
example : ∑ x ∈ piAntidiag univ 3, multinomialReal 3 (fun _ : Fin 2 => (1 : ℝ)) x = 8 := by
  rw [sum_multinomialReal_eq_pow]
  norm_num

/-- The mean and variance of one cell for `p = (1/2, 1/4, 1/4)`, `N = 4`: `E X₀ = 2` and
`Var X₀ = 4 · 1/2 · 1/2 = 1`. -/
example :
    ∑ x ∈ piAntidiag (univ : Finset (Fin 3)) (4 : ℕ),
        ((x 0 : ℕ) : ℝ) * multinomialReal 4 ![(1 / 2 : ℝ), 1 / 4, 1 / 4] x = 2 ∧
      ∑ x ∈ piAntidiag (univ : Finset (Fin 3)) (4 : ℕ),
        (((x 0 : ℕ) : ℝ) - (4 : ℕ) * (1 / 2)) * (((x 0 : ℕ) : ℝ) - (4 : ℕ) * (1 / 2)) *
          multinomialReal 4 ![(1 / 2 : ℝ), 1 / 4, 1 / 4] x = 1 := by
  have hp : ∑ i, ![(1 / 2 : ℝ), 1 / 4, 1 / 4] i = 1 := by
    simp [Fin.sum_univ_three]; norm_num
  have hp₀ : ∀ i, 0 ≤ ![(1 / 2 : ℝ), 1 / 4, 1 / 4] i := by
    intro i; fin_cases i <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [sum_mul_multinomialReal hp hp₀]; norm_num
  · have h := sum_covariance_multinomialReal (N := 4) hp hp₀ 0 0
    simp only [ite_true] at h
    convert h using 1
    simp
    norm_num

/-- Distinct cells are negatively correlated: `Cov(X₀, X₁) = -N p₀ p₁`. -/
example {N : ℕ} {p : Fin 3 → ℝ} (hp : ∑ i, p i = 1) (hp₀ : ∀ i, 0 ≤ p i) :
    ∑ x ∈ piAntidiag univ N, ((x 0 : ℝ) - N * p 0) * ((x 1 : ℝ) - N * p 1) * multinomialReal N p x
      = -(N * p 0 * p 1) := by
  rw [sum_covariance_multinomialReal hp hp₀]
  simp
  ring

/-- The multinomial PMF is defined for a probability vector. -/
noncomputable example : PMF (Fin 3 → ℕ) :=
  multinomial 5 ![1 / 2, 1 / 4, 1 / 4] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)

/-- Non-vacuity of Poisson conditioning: the coordinates of the product of Poisson laws
`⊗ᵢ Po(rᵢ)` on `ι → ℕ` are independent with laws `Po(rᵢ)`. -/
theorem witness_pi {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) :
    (∀ i, HasLaw (fun ω : ι → ℕ => ω i) (poissonMeasure (r i))
        (Measure.pi fun i => poissonMeasure (r i))) ∧
      iIndepFun (fun i (ω : ι → ℕ) => ω i) (Measure.pi fun i => poissonMeasure (r i)) :=
  ⟨fun i => (measurePreserving_eval (fun i => poissonMeasure (r i)) i).hasLaw,
    iIndepFun_pi (X := fun _ => id) fun _ => measurable_id.aemeasurable⟩

/-- On the witness, independent `Po(1)`, `Po(2)`, `Po(1)` counts given total `2` land as
`(1, 1, 0)` with probability `2 · (1/4) (1/2) = 1/4`. -/
example :
    ((Measure.pi fun i : Fin 3 => poissonMeasure (![1, 2, 1] i))[|
      {ω : Fin 3 → ℕ | ∑ i, ω i = 2}]).real {ω | ∀ i, ω i = ![1, 1, 0] i} = 1 / 4 := by
  have h := witness_pi (![1, 2, 1] : Fin 3 → ℝ≥0)
  rw [cond_measureReal_eq_multinomialReal (X := fun i (ω : Fin 3 → ℕ) => ω i)
    (fun i => measurable_pi_apply i) h.1 h.2 (by simp [Fin.sum_univ_three]) 2 ![1, 1, 0],
    multinomialReal_eq_factorial_div (by simp [Fin.sum_univ_three])]
  simp [Fin.prod_univ_three, Fin.sum_univ_three]
  norm_num

/-- Non-vacuity of the two-cell case: the coordinates of `Po(a) ⊗ Po(b)`. -/
theorem witness_prod (a b : ℝ≥0) :
    HasLaw (fun ω : ℕ × ℕ => ω.1) (poissonMeasure a) ((poissonMeasure a).prod (poissonMeasure b))
      ∧ HasLaw (fun ω : ℕ × ℕ => ω.2) (poissonMeasure b)
        ((poissonMeasure a).prod (poissonMeasure b)) ∧
      IndepFun (fun ω : ℕ × ℕ => ω.1) (fun ω : ℕ × ℕ => ω.2)
        ((poissonMeasure a).prod (poissonMeasure b)) :=
  ⟨measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id⟩

/-- On the witness with `a = b = 1`, `P(X = 1 | X + Y = 2) = C(2, 1) / 4 = 1/2`. -/
example :
    (((poissonMeasure 1).prod (poissonMeasure 1))[|{ω : ℕ × ℕ | ω.1 + ω.2 = 2}]).real
      {ω | ω.1 = 1} = 1 / 2 := by
  have h := witness_prod 1 1
  rw [cond_measureReal_eq_binomial (by norm_num) measurable_fst measurable_snd h.1 h.2.1 h.2.2,
    binomial_real_singleton]
  norm_num [Nat.choose]

end MathlibExtTest.Probability.Distributions.Multinomial
