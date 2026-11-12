/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountPooled
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset
open scoped Nat
open MathlibExt.Biology.Omics.HierarchicalCount
open MathlibExt.Biology.Omics.HierarchicalCountPooled

namespace MathlibExtTest.Biology.Omics.HierarchicalCountPooled

/-- One cell: the pooled likelihood is the one-cell Poisson likelihood. -/
example (s : Fin 1 → ℝ) (k : Fin 1 → ℕ) (r : ℝ) :
    pooledLik s k r = poissonExposureLik (s 0) (k 0) r := by
  simp [pooledLik]

/-- No cells (boundary): the joint likelihood is `1` and the pooled posterior is the prior
`Gamma(a, b)`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Fin 0 → ℝ) (k : Fin 0 → ℕ) (r : ℝ) :
    pooledLik s k r = 1 ∧
      pooledLik s k r * gammaPDFReal a b r / pooledMarginalLik a b s k = gammaPDFReal a b r := by
  refine ⟨by simp [pooledLik], ?_⟩
  simpa using pooledPosterior_eq_gammaPDFReal ha hb (s := s) (fun j => j.elim0) k r

/-- Two cells with size factors `1, 2` and counts `1, 3`, prior `Gamma(3, 1)`: the pooled
posterior is `Gamma(3 + 4, 1 + 3) = Gamma(7, 4)`. -/
example (r : ℝ) :
    pooledLik ![1, 2] ![1, 3] r * gammaPDFReal 3 1 r / pooledMarginalLik 3 1 ![1, 2] ![1, 3] =
      gammaPDFReal 7 4 r := by
  have h := pooledPosterior_eq_gammaPDFReal (a := 3) (b := 1) (s := ![(1 : ℝ), 2]) (by norm_num)
    (by norm_num) (fun j => by fin_cases j <;> norm_num) ![1, 3] r
  norm_num [Fin.sum_univ_two] at h
  exact h

/-- The cell-split factor at two equal cells and counts `(1, 1)` is the multinomial mass
`2 · (1/2)²  = 1/2`, computed from the definition, and the factorization holds there. -/
example (r : ℝ) :
    multinomialReal (∑ j, (![1, 1] : Fin 2 → ℕ) j) (fun j => (![1, 1] : Fin 2 → ℝ) j /
      ∑ i, (![1, 1] : Fin 2 → ℝ) i) ![1, 1] = 1 / 2 ∧
      pooledLik ![1, 1] ![1, 1] r = 1 / 2 * poissonExposureLik 2 2 r := by
  have hm : multinomialReal (∑ j, (![1, 1] : Fin 2 → ℕ) j) (fun j => (![1, 1] : Fin 2 → ℝ) j /
      ∑ i, (![1, 1] : Fin 2 → ℝ) i) ![1, 1] = 1 / 2 := by
    rw [multinomialReal, ite_eq_left rfl, Nat.multinomial_univ_two]
    norm_num [Fin.sum_univ_two, Fin.prod_univ_two]
  refine ⟨hm, ?_⟩
  rw [pooledLik_eq_multinomialReal_mul (fun j => by fin_cases j <;> norm_num), hm]
  norm_num [Fin.sum_univ_two]

/-- A zero pooled count: with two unit cells and prior `Gamma(2, 2)`, `P(K = 0)` is the
`NB(2, 2)` zero mass `(2 / 4)² = 1 / 4`; the only split of `0` is the zero vector. -/
example : ∑ k ∈ piAntidiag univ 0, pooledMarginalLik 2 2 (![1, 1] : Fin 2 → ℝ) k = 1 / 4 := by
  rw [sum_pooledMarginalLik (by norm_num) (by norm_num) (fun j => by fin_cases j <;> norm_num)]
  norm_num [negBinomialReal, Fin.sum_univ_two, show (2 : ℝ) = (2 : ℕ) by norm_num,
    Real.rpow_natCast]

/-- Pooling more exposure gives strictly less shrinkage: `1 / 2 < 2 / 3`. -/
example : shrinkageWeight 1 1 < shrinkageWeight 1 2 ∧ shrinkageWeight 1 1 = 1 / 2 ∧
    shrinkageWeight 1 2 = 2 / 3 := by
  refine ⟨shrinkageWeight_strictMonoOn one_pos (Set.mem_Ici.2 zero_le_one)
    (Set.mem_Ici.2 zero_le_two) one_lt_two, ?_, ?_⟩ <;> norm_num [shrinkageWeight]

/-- Deterministic posterior consistency on a concrete sequence: exposure `n` and pooled count
`2 n`, so `K / S → 2`; the posterior mean tends to `2` for any prior. -/
example (a b : ℝ) :
    Tendsto (fun n : ℕ => posteriorMean a b n (2 * n)) atTop (𝓝 2) := by
  refine (tendsto_posteriorMean_of_tendsto (K := fun n => 2 * n) tendsto_natCast_atTop_atTop
    (tendsto_const_nhds.congr' ?_)).1
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  push_cast
  field_simp

/-- Almost-sure posterior consistency is not vacuous: constant cell counts `3` at size factor
`1` (independent and identically distributed) have mean `1 · 3`, so on any probability space the
pooled posterior mean tends to `3` almost surely. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (a b : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorMean a b (∑ _j : Fin n, (1 : ℝ))
      (∑ _j : Fin n, (fun (_ : ℕ) (_ : Ω) => 3) _j ω)) atTop (𝓝 3) := by
  have h := ae_tendsto_pooledPosterior (μ := μ) (X := fun _ _ => 3) (a := a) (b := b) (s := 1)
    (r₀ := 3) one_pos (integrable_const _) (fun i j _ => indepFun_const_left 3 _)
    (fun j => IdentDistrib.refl aemeasurable_const) (by simp)
  filter_upwards [h] with ω hω
  exact hω.1

/-- `ae_tendsto_pooledEB` applies to a concrete sequence: the coordinates of the infinite
product of the pooled-count law (two cells, size factors `1, 2`) are i.i.d. with that law, so
almost surely the empirical-Bayes posterior mean from their pooled counts tends to the oracle
pooled posterior mean `(a + K) / (b + 3)`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ μ : Measure (ℕ → ℕ), IsProbabilityMeasure μ ∧ ∀ᵐ ω ∂μ, ∀ K : ℕ,
      Tendsto (fun n => ebPosteriorMean (∑ j, (![1, 2] : Fin 2 → ℝ) j)
        (sampleMean (fun i ω => ((ω i : ℕ) : ℝ)) n ω) (sampleVar (fun i ω => ((ω i : ℕ) : ℝ)) n ω)
        K) atTop (𝓝 (posteriorMean a b (∑ j, (![1, 2] : Fin 2 → ℝ) j) K)) := by
  have hs : ∀ j, 0 < (![1, 2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> norm_num
  have hm : 0 ≤ (∑ j, (![1, 2] : Fin 2 → ℝ) j) * a / b :=
    div_nonneg (mul_nonneg (sum_nonneg fun j _ => (hs j).le) ha.le) hb.le
  set p : ℕ → ℝ := fun K => ∑ k ∈ piAntidiag univ K, pooledMarginalLik a b ![1, 2] k
  have hpNB : p = negBinomialReal a ((∑ j, (![1, 2] : Fin 2 → ℝ) j) * a / b) :=
    funext fun K => sum_pooledMarginalLik ha hb hs K
  have hp : HasSum p 1 := hpNB ▸ hasSum_negBinomialReal ha hm
  have hp0 : ∀ K, 0 ≤ p K := fun K => hpNB ▸ negBinomialReal_nonneg ha hm K
  let ν : Measure ℕ := Measure.sum fun K => ENNReal.ofReal (p K) • Measure.dirac K
  have hν : ∀ K, ν {K} = ENNReal.ofReal (p K) := fun K => Measure.sum_smul_dirac_singleton
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hp0 hp.summable, hp.tsum_eq, ENNReal.ofReal_one]⟩
  refine ⟨Measure.infinitePi fun _ : ℕ => ν, inferInstance, ?_⟩
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => id)
    (fun _ => measurable_id)
  have h := ae_tendsto_pooledEB (N := fun i (ω : ℕ → ℕ) => ω i) ha hb hs (measurable_pi_apply 0)
    (fun i j hij => hind.indepFun hij)
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩)
    (fun K => by
      rw [← map_measureReal_apply (measurable_pi_apply 0) (measurableSet_singleton K),
        Measure.infinitePi_map_eval, measureReal_def, hν, ENNReal.toReal_ofReal (hp0 K)])
  filter_upwards [h] with ω hω
  exact hω.2.2

end MathlibExtTest.Biology.Omics.HierarchicalCountPooled
