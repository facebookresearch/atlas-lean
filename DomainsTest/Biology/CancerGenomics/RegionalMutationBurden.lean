/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.CancerGenomics.RegionalMutationBurden
import Domains.Biology.Omics.HierarchicalCount
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Tests for the gamma-Poisson model of mutation counts in a region.

Region `A` has predicted mean `μ = 2` and variance `σ² = 4`, so shape `α = 1` and scale
`θ = 2`: its rate is exponential with mean `2`. Its three possible mutations have probabilities
`1/2, 1/4, 1/4`; the candidate set `I = {0, 1}` has `∑_I p = 3/4`, and with `C = 2/3` the success
probability is `1 / (1 + (2/3) · 2 · (3/4)) = 1/2`. Region `B` has `μ = 3`, `σ² = 9` (`α = 1`,
`θ = 3`), uniform probabilities `1/3` and candidate set `{2}`, so its success probability is
`1 / (1 + (2/3) · 3 · (1/3)) = 3/5`.

* the rate law has mean `2` and variance `4`;
* ground truth: the count of region `A` is geometric, `P(N = k) = (1/2)^(k+1)`, and the `p`-value
  of an observed count `2` is `1/4`;
* with `C = 0` the count is `0` almost surely;
* the model agrees with the gamma-Poisson hierarchy with exposure of
  `Domains.Biology.Omics.HierarchicalCount`;
* over the union of regions `A` and `B`, `P(N = 1) = (1/2)(6/25) + (1/4)(3/5) = 27/100`;
* two regions with a common success probability give the negative binomial law with the summed
  shape. -/

open MeasureTheory ProbabilityTheory Finset Domains.Biology.CancerGenomics.RegionalMutationBurden

namespace DomainsTest.Biology.CancerGenomics.RegionalMutationBurden

/-- The mutation probabilities of region `A`. -/
noncomputable def pA : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The candidate set of region `A`. -/
def IA : Finset (Fin 3) := {0, 1}

/-- The mutation probabilities of region `B`. -/
noncomputable def pB : Fin 3 → ℝ := fun _ => 1 / 3

/-- The candidate set of region `B`. -/
def IB : Finset (Fin 3) := {2}

theorem pA_nonneg : ∀ i ∈ IA, 0 ≤ pA i := by
  intro i _
  fin_cases i <;> norm_num [pA]

theorem pB_nonneg : ∀ i ∈ IB, 0 ≤ pB i := fun _ _ => by norm_num [pB]

theorem sum_pA : ∑ i ∈ IA, pA i = 3 / 4 := by
  norm_num [IA, pA]

theorem sum_pB : ∑ i ∈ IB, pB i = 1 / 3 := by
  norm_num [IB, pB]

/-- The rate law of region `A` has mean `2` and variance `4`. -/
example : ∫ x, x ∂rateLaw 2 4 = 2 ∧ variance id (rateLaw 2 4) = 4 :=
  ⟨integral_id_rateLaw (by norm_num) (by norm_num),
    variance_id_rateLaw (by norm_num) (by norm_num)⟩

/-- The count of region `A` is geometric with success probability `1/2`. -/
theorem countPMF_A (k : ℕ) : countPMF 2 4 (2 / 3) pA IA k = (1 / 2) ^ (k + 1) := by
  rw [countPMF_eq_negBinomialPMF (by norm_num) (by norm_num) (by norm_num) pA_nonneg, sum_pA,
    negBinomialPMF]
  norm_num [ascPochhammer_eval_one, pow_succ]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The `p`-value of an observed count `2` in region `A` is `P(N ≥ 2) = 1/4`. -/
example : ∑' k, countPMF 2 4 (2 / 3) pA IA (k + 2) = 1 / 4 := by
  rw [tsum_countPMF_add (by norm_num) (by norm_num) (by norm_num) pA_nonneg, sum_pA]
  norm_num [Finset.sum_range_succ, negBinomialPMF, ascPochhammer_eval_one]

/-- With no cohort scaling the count is `0` almost surely. -/
example (k : ℕ) : countPMF 2 4 0 pA IA k = if k = 0 then 1 else 0 := by
  rw [countPMF_eq_negBinomialPMF (by norm_num) (by norm_num) le_rfl pA_nonneg]
  rcases k with _ | k <;> simp [negBinomialPMF]

/-- The model is the gamma-Poisson hierarchy with exposure `C ∑_I p` and gamma rate `μ / σsq`. -/
example {μ σsq C : ℝ} {ι : Type*} {p : ι → ℝ} {I : Finset ι} (hμ : 0 < μ) (hσ : 0 < σsq)
    (hC : 0 ≤ C) (hp : ∀ i ∈ I, 0 ≤ p i) (k : ℕ) :
    countPMF μ σsq C p I k =
      MathlibExt.Biology.Omics.HierarchicalCount.marginalLik (μ ^ 2 / σsq) (μ / σsq)
        (C * ∑ i ∈ I, p i) k := by
  have hs : 0 ≤ C * ∑ i ∈ I, p i := mul_nonneg hC (sum_nonneg hp)
  rw [countPMF_eq_negBinomialPMF hμ hσ hC hp,
    MathlibExt.Biology.Omics.HierarchicalCount.marginalLik_eq_negBinomialReal (by positivity)
      (by positivity) hs,
    negBinomialReal_eq_negBinomialPMF (by positivity) (by positivity)]
  congr 1
  field_simp

/-- The predicted means of regions `A` and `B`. -/
noncomputable def μAB : Fin 2 → ℝ := ![2, 3]

/-- The predicted variances of regions `A` and `B`. -/
noncomputable def σsqAB : Fin 2 → ℝ := ![4, 9]

/-- The mutation probabilities of regions `A` and `B`. -/
noncomputable def pAB : Fin 2 → Fin 3 → ℝ := ![pA, pB]

/-- The candidate sets of regions `A` and `B`. -/
def IAB : Fin 2 → Finset (Fin 3) := ![IA, IB]

/-- Over the union of regions `A` and `B`, one mutation is observed with probability
`P(N_A = 0) P(N_B = 1) + P(N_A = 1) P(N_B = 0) = (1/2)(6/25) + (1/4)(3/5) = 27/100`. -/
example : unionCountPMF μAB σsqAB (2 / 3) pAB IAB 1 = 27 / 100 := by
  have hμ : ∀ r, 0 < μAB r := fun r => by fin_cases r <;> norm_num [μAB]
  have hσ : ∀ r, 0 < σsqAB r := fun r => by fin_cases r <;> norm_num [σsqAB]
  have hp : ∀ r, ∀ i ∈ IAB r, 0 ≤ pAB r i := fun r => by
    fin_cases r
    · exact pA_nonneg
    · exact pB_nonneg
  rw [unionCountPMF_eq_sum_prod_negBinomialPMF hμ hσ (by norm_num) hp,
    piAntidiag_univ_fin_eq_antidiagonalTuple, Finset.Nat.antidiagonalTuple_two, sum_map]
  simp only [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_cons,
    Fin.prod_univ_two]
  simp [μAB, σsqAB, pAB, IAB, sum_pA, sum_pB, negBinomialPMF]
  norm_num

/-- Two regions whose candidate sets have a common success probability `q`: the total count is
negative binomial with success probability `q` and the summed shape. This is the convolution
identity `ProbabilityTheory.sum_negBinomialPMF_mul`. -/
example {μ σsq : Fin 2 → ℝ} {C : ℝ} {p : Fin 2 → Fin 3 → ℝ} {I : Fin 2 → Finset (Fin 3)}
    (hμ : ∀ r, 0 < μ r) (hσ : ∀ r, 0 < σsq r) (hC : 0 ≤ C) (hp : ∀ r, ∀ i ∈ I r, 0 ≤ p r i)
    {q : ℝ} (hq : 0 < q) (hcommon : ∀ r, 1 / (1 + C * (σsq r / μ r) * ∑ i ∈ I r, p r i) = q)
    (k : ℕ) :
    unionCountPMF μ σsq C p I k =
      negBinomialPMF (μ 0 ^ 2 / σsq 0 + μ 1 ^ 2 / σsq 1) q k := by
  rw [unionCountPMF_eq_sum_prod_negBinomialPMF hμ hσ hC hp,
    piAntidiag_univ_fin_eq_antidiagonalTuple, Finset.Nat.antidiagonalTuple_two, sum_map,
    ← sum_negBinomialPMF_mul _ _ hq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun j _ => ?_
  simp [Fin.prod_univ_two, hcommon]

end DomainsTest.Biology.CancerGenomics.RegionalMutationBurden
