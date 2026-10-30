/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.FineMapping

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open MathlibExt.Biology.StatisticalGenetics.FineMapping
open scoped NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.FineMapping

/-! ### Wakefield's ABF -/

/-- A zero prior variance makes the alternative the null: `ABF = 1`. -/
example {V : ℝ≥0} (hV : V ≠ 0) (b : ℝ) : wakefieldABF V 0 b = 1 := by
  rw [wakefieldABF, add_zero, div_self (gaussianPDFReal_pos _ _ _ hV).ne']

/-- At `z = 0` the ABF is the shrinkage factor `√(V / (V + W))`, here `√(1 / 2)`. -/
example : wakefieldABF 1 1 0 = √(1 / 2) := by
  rw [wakefieldABF_eq one_ne_zero]
  norm_num

/-- Outside the domain (`V = 0`) the definition is Lean's junk value `0`. -/
example (W : ℝ≥0) (b : ℝ) : wakefieldABF 0 W b = 0 := by
  simp [wakefieldABF, gaussianPDFReal_zero_var]

/-! ### Single-effect regression -/

/-- Posterior inclusion probabilities with a uniform prior are proportional to the Bayes
factors. -/
example : pip ![1 / 2, 1 / 2] ![1, 3] 1 = 3 / 4 := by
  simp [pip, Fin.sum_univ_two]
  norm_num

/-- The least-squares estimate of `y = x` on `x ≠ 0` is `1`. -/
example {n : Type*} [Fintype n] {x : EuclideanSpace ℝ n} (hx : x ≠ 0) : olsEffect x x = 1 := by
  rw [olsEffect, real_inner_self_eq_norm_sq, div_self (by positivity)]

/-- Outside the domain (`x = 0`) the estimate is Lean's junk value `0`. -/
example {n : Type*} [Fintype n] (y : EuclideanSpace ℝ n) : olsEffect 0 y = 0 := by
  simp [olsEffect]

/-- The covariance of the single-effect model is positive definite for `σ² > 0`. -/
example (x : EuclideanSpace ℝ (Fin 3)) : (serCov 1 2 x).PosDef :=
  posDef_serCov one_ne_zero 2 x

/-! ### coloc -/

/-- **Non-vacuity witness** for `ColocPrior`: the default priors of the coloc package,
`p1 = p2 = 10⁻⁴` and `p12 = 10⁻⁵`, on two variants. -/
noncomputable def defaultPrior : ColocPrior (Fin 2) where
  p1 := 1 / 10 ^ 4
  p2 := 1 / 10 ^ 4
  p12 := 1 / 10 ^ 5
  p1_nonneg := by norm_num
  p2_nonneg := by norm_num
  p12_nonneg := by norm_num
  sum_le_one := by simp; norm_num

example : colocHypothesis ((some 0, some 0) : Option (Fin 2) × Option (Fin 2)) = .h4 := rfl

example : colocHypothesis ((some 0, some 1) : Option (Fin 2) × Option (Fin 2)) = .h3 := rfl

/-- With all Bayes factors equal to `1`, the H4 closed form is `p12` times the number of
variants. -/
example : colocClosedForm defaultPrior 1 1 .h4 = 2 / 10 ^ 5 := by
  simp [colocClosedForm, defaultPrior]
  norm_num

/-- The priors of the witness sum to one. -/
example : ∑ S, defaultPrior.prior S = 1 := defaultPrior.sum_prior

/-- The H3 sum by brute force, for two variants with Bayes factors `(2, 3)` and `(5, 7)`:
`p1 p2 (2 · 7 + 3 · 5)`. -/
example : ∑ S ∈ Finset.univ.filter (fun S => colocHypothesis S = .h3),
    defaultPrior.prior S * colocBF ![2, 3] ![5, 7] S = 29 / 10 ^ 8 := by
  rw [sum_colocPrior_mul_colocBF]
  simp [colocClosedForm, defaultPrior, Fin.sum_univ_two]
  norm_num

/-! ### Credible sets -/

/-- Inclusion probabilities `(0.5, 0.3, 0.2)`, already sorted. -/
noncomputable def α3 : Fin 3 → ℝ := ![1 / 2, 3 / 10, 1 / 5]

/-- The identity order, viewed as an enumeration of `Fin 3` by `Fin (card (Fin 3))`. -/
def σ3 : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := finCongr (Fintype.card_fin 3)

theorem antitone_α3 : Antitone (α3 ∘ σ3) := by
  refine Antitone.comp_monotone ?_ fun i j h => h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [α3, Fin.le_def] <;> norm_num

/-- `{0, 1}` is a `0.8`-credible set. -/
example : IsCredibleSet α3 (4 / 5) {0, 1} := by
  simp [IsCredibleSet, α3]
  norm_num

/-- Every `0.8`-credible set has at least two variants, since no prefix of length `< 2` has
mass `0.8`. -/
example (S : Finset (Fin 3)) (hS : IsCredibleSet α3 (4 / 5) S) : 2 ≤ S.card := by
  refine le_card_of_isCredibleSet α3 antitone_α3 (fun m hm => ?_) hS
  interval_cases m
  · simp [IsCredibleSet, sortedPrefix]
  · rw [show sortedPrefix σ3 1 = {0} by decide]
    simp [IsCredibleSet, α3]
    norm_num

#print axioms wakefieldABF_eq
#print axioms rnDeriv_map_add_ae_eq
#print axioms multivariateGaussianPDFReal_serCov_div
#print axioms serPosterior_eq_pip
#print axioms condDistrib_ser_effect
#print axioms sum_colocPrior_mul_colocBF
#print axioms exists_minimal_credible_prefix

end MathlibExtTest.Biology.StatisticalGenetics.FineMapping
