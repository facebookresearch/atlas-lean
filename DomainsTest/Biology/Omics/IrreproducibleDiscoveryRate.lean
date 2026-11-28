/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.IrreproducibleDiscoveryRate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-! Tests for the copula mixture model and the irreproducible discovery rate.

* `ρ = 1`: three findings with latent pairs `(2, 2)`, `(0, 1)` and `(3, 3)`; the first and the last
  lie on the diagonal, where all the reproducible findings lie, so their local rates are `0`, and
  the middle one's is `1`. The rates of the sets `{0, 2}`, `{0, 1, 2}` and `∅` are `0`, `1/3`
  and `0`, and the bounds and the monotonicity theorem apply.
* Two identical components (`μ = 0`, `σ = 1`, `ρ = 0`) with `π₁ = 1/2`: the latent pair carries
  no information about the label, and every local rate is the prior `1/2`.
* `π₁ = 0` and `π₁ = 1`: every finding is irreproducible, or reproducible, and the local rates
  are `1`, or `0`.
* Swapping the two replicates leaves the local rate unchanged.
* The posterior, latent-marginal and expected-fraction theorems apply to concrete parameters,
  with `ρ = 1` and with `ρ < 1`. -/

open MeasureTheory ProbabilityTheory
open Domains.Biology.Omics.IrreproducibleDiscoveryRate

namespace DomainsTest.Biology.Omics.IrreproducibleDiscoveryRate

/-- Three findings: two on the diagonal and one off it. -/
noncomputable def z : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![!₂[2, 2], !₂[0, 1], !₂[3, 3]]

/-! ### `ρ = 1` -/

example : irreproducibleDiscoveryRate (1 / 2) 1 1 1 z {0} = 0 := by
  simp [irreproducibleDiscoveryRate_singleton_of_eq_one, z]

example : irreproducibleDiscoveryRate (1 / 2) 1 1 1 z {1} = 1 := by
  simp [irreproducibleDiscoveryRate_singleton_of_eq_one, z]

example : irreproducibleDiscoveryRate (1 / 2) 1 1 1 z {0, 2} = 0 := by
  rw [irreproducibleDiscoveryRate_eq_sum_div]
  simp [irreproducibleDiscoveryRate_singleton_of_eq_one, z]

example : irreproducibleDiscoveryRate (1 / 2) 1 1 1 z Finset.univ = 1 / 3 := by
  rw [irreproducibleDiscoveryRate_eq_sum_div]
  simp [irreproducibleDiscoveryRate_singleton_of_eq_one, z, Fin.sum_univ_three]

example : irreproducibleDiscoveryRate (1 / 2) 1 1 1 z ∅ = 0 := by
  simp [irreproducibleDiscoveryRate]

/-- Adding the off-diagonal finding to the two diagonal ones raises the rate from `0` to `1/3`, as
the monotonicity theorem says it cannot lower it. -/
example : irreproducibleDiscoveryRate (1 / 2) 1 1 1 z {0, 2} ≤
    irreproducibleDiscoveryRate (1 / 2) 1 1 1 z Finset.univ := by
  refine irreproducibleDiscoveryRate_le_of_subset (Finset.subset_univ _) (by simp) ?_
  intro i hi j _ hj
  fin_cases i <;> fin_cases j <;> simp_all [irreproducibleDiscoveryRate_singleton_of_eq_one, z]

example (S : Finset (Fin 3)) : 0 ≤ irreproducibleDiscoveryRate (1 / 2) 1 1 1 z S ∧
    irreproducibleDiscoveryRate (1 / 2) 1 1 1 z S ≤ 1 :=
  ⟨irreproducibleDiscoveryRate_nonneg (by norm_num) S,
    irreproducibleDiscoveryRate_le_one (by norm_num) S⟩

/-! ### Two identical components -/

/-- With `μ = 0`, `σ = 1` and `ρ = 0` the two components are both the standard bivariate normal,
and every local rate is the prior probability `1 - π₁ = 1/2`. -/
example (x : EuclideanSpace ℝ (Fin 2)) :
    irreproducibleDiscoveryRate (1 / 2) 0 1 0 id {x} = 1 / 2 := by
  rw [irreproducibleDiscoveryRate_singleton_of_ne_one (by norm_num)]
  have : 0 < Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / 2) / (2 * Real.pi) := by positivity
  simp only [id, sub_zero, mul_zero, zero_mul, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Real.sqrt_one] at this ⊢
  field_simp
  ring_nf

/-! ### No reproducible, or only reproducible, findings -/

example (x : EuclideanSpace ℝ (Fin 2)) :
    irreproducibleDiscoveryRate 0 1 1 (1 / 2) id {x} = 1 := by
  rw [irreproducibleDiscoveryRate_singleton_of_ne_one (by norm_num)]
  have : 0 < Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / 2) / (2 * Real.pi) := by positivity
  simp only [id, sub_zero, one_mul, zero_mul, add_zero]
  exact div_self this.ne'

example (x : EuclideanSpace ℝ (Fin 2)) :
    irreproducibleDiscoveryRate 1 1 1 (1 / 2) id {x} = 0 := by
  rw [irreproducibleDiscoveryRate_singleton_of_ne_one (by norm_num)]
  simp

/-! ### Exchangeable replicates -/

/-- Swapping the latent scores of the two replicates leaves the local rate unchanged. -/
example (π₁ μ σ ρ u v : ℝ) :
    irreproducibleDiscoveryRate π₁ μ σ ρ id {!₂[u, v]} =
      irreproducibleDiscoveryRate π₁ μ σ ρ id {!₂[v, u]} := by
  by_cases hρ : ρ = 1
  · subst hρ
    simp only [irreproducibleDiscoveryRate_singleton_of_eq_one, id]
    simp [eq_comm]
  · rw [irreproducibleDiscoveryRate_singleton_of_ne_one hρ,
      irreproducibleDiscoveryRate_singleton_of_ne_one hρ]
    simp only [id, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring_nf

/-! ### The posterior, the latent marginal and the expected fraction -/

example {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B) :
    let P : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
      ENNReal.ofReal (1 - 1 / 2) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
        ENNReal.ofReal (1 / 2) • (Measure.dirac 1).prod
          (multivariateGaussian !₂[2, 2] !![1 ^ 2, 1 * 1 ^ 2; 1 * 1 ^ 2, 1 ^ 2])
    P ({0} ×ˢ B) = ∫⁻ x in B, ENNReal.ofReal (irreproducibleDiscoveryRate (1 / 2) 2 1 1 id {x})
      ∂(P.map Prod.snd) :=
  irreproducibleDiscoveryRate_posterior (by norm_num) (by norm_num) (by norm_num) hB

example {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B) :
    let P : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
      ENNReal.ofReal (1 - 1 / 5) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
        ENNReal.ofReal (1 / 5) • (Measure.dirac 1).prod
          (multivariateGaussian !₂[3, 3] !![2 ^ 2, (4 / 5) * 2 ^ 2; (4 / 5) * 2 ^ 2, 2 ^ 2])
    P ({0} ×ˢ B) = ∫⁻ x in B,
      ENNReal.ofReal (irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) id {x}) ∂(P.map Prod.snd) :=
  irreproducibleDiscoveryRate_posterior (by norm_num) (by norm_num) (by norm_num) hB

example (t : ℝ) :
    cdf ((ENNReal.ofReal (1 - 1 / 5) • multivariateGaussian 0 1 +
        ENNReal.ofReal (1 / 5) • multivariateGaussian !₂[3, 3]
          !![2 ^ 2, (4 / 5) * 2 ^ 2; (4 / 5) * 2 ^ 2, 2 ^ 2]).map
        fun x : EuclideanSpace ℝ (Fin 2) => x 1) t =
      (1 - 1 / 5) * cdf (gaussianReal 0 1) t + 1 / 5 * cdf (gaussianReal 0 1) ((t - 3) / 2) :=
  cdf_latent_coordinate (by norm_num) (by norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num) 1 t

/-- Selecting the findings whose local rate is at most `α` gives a set whose rate is at most `α`,
so the expected fraction of irreproducible findings in it is at most `α`. -/
example {α : ℝ} (hα : 0 ≤ α) :
    let P : Measure (Fin 2 × EuclideanSpace ℝ (Fin 2)) :=
      ENNReal.ofReal (1 - 1 / 5) • (Measure.dirac 0).prod (multivariateGaussian 0 1) +
        ENNReal.ofReal (1 / 5) • (Measure.dirac 1).prod
          (multivariateGaussian !₂[3, 3] !![2 ^ 2, (4 / 5) * 2 ^ 2; (4 / 5) * 2 ^ 2, 2 ^ 2])
    ∫⁻ ω, ENNReal.ofReal
        ((((Finset.univ.filter fun i : Fin 3 =>
            irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) (fun j => (ω j).2) {i} ≤ α).filter
          fun i => (ω i).1 = 0).card : ℝ) /
          (Finset.univ.filter fun i : Fin 3 =>
            irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) (fun j => (ω j).2) {i} ≤ α).card)
        ∂Measure.pi (fun _ : Fin 3 => P) ≤ ENNReal.ofReal α := by
  intro P
  refine lintegral_fraction_irreproducible_le (μ := 3) (σ := 2) (ρ := 4 / 5) (by norm_num)
    (by norm_num) (by norm_num)
    (fun z => Finset.univ.filter fun i => irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) z {i} ≤ α)
    (fun s => ?_) (fun z => ?_)
  · have : {z : Fin 3 → EuclideanSpace ℝ (Fin 2) | (Finset.univ.filter fun i =>
        irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) z {i} ≤ α) = s} =
        ⋂ i : Fin 3, {z | irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) z {i} ≤ α ↔ i ∈ s} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.ext_iff, Finset.mem_filter,
        Finset.mem_univ, true_and]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ s
    · simpa [hi] using measurableSet_le (measurable_irreproducibleDiscoveryRate {i})
        measurable_const
    · simpa [hi] using measurableSet_lt measurable_const
        (measurable_irreproducibleDiscoveryRate (π₁ := 1 / 5) (μ := 3) (σ := 2) (ρ := 4 / 5) {i})
  · rw [irreproducibleDiscoveryRate_eq_sum_div]
    rcases (Finset.univ.filter fun i => irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) z {i} ≤ α
      ).eq_empty_or_nonempty with h | h
    · rw [h]; simpa using hα
    · rw [div_le_iff₀ (by exact_mod_cast h.card_pos)]
      calc _ ≤ ∑ _i ∈ Finset.univ.filter fun i =>
              irreproducibleDiscoveryRate (1 / 5) 3 2 (4 / 5) z {i} ≤ α, α :=
            Finset.sum_le_sum fun i hi => (Finset.mem_filter.1 hi).2
        _ = _ := by simp [mul_comm]

end DomainsTest.Biology.Omics.IrreproducibleDiscoveryRate
