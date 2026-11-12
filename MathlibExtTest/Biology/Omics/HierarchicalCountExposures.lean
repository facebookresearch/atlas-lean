/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountExposures
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped Nat NNReal
open MathlibExt.Biology.Omics.HierarchicalCount
open MathlibExt.Biology.Omics.HierarchicalCountExposures

namespace MathlibExtTest.Biology.Omics.HierarchicalCountExposures

/-! ### Joint likelihood, computed from the definition -/

/-- Two cells with exposures `1, 2` and counts `0, 1`: by the definition of
`poissonExposureLik`, the joint likelihood is `e^{-r} · 2 r e^{-2 r} = 2 r e^{-3 r}`. -/
example (r : ℝ) :
    ∏ i : Fin 2, poissonExposureLik (![1, 2] i) (![0, 1] i) r = 2 * r * exp (-(3 * r)) := by
  simp only [Fin.prod_univ_two, poissonExposureLik, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : exp (-(3 * r)) = exp (-(1 * r)) * exp (-(2 * r)) := by rw [← Real.exp_add]; ring_nf
  rw [this]
  simp only [one_mul, pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    div_one, mul_one]
  ring

/-- The factorization theorem agrees with the direct computation above: the rate-free constant
is `(1⁰/0!) (2¹/1!) = 2`, `K = 1`, `S = 3`. -/
example (r : ℝ) :
    ∏ i : Fin 2, poissonExposureLik (![1, 2] i) (![0, 1] i) r = 2 * r * exp (-(3 * r)) := by
  rw [prod_poissonExposureLik]
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

/-! ### Pooled conjugacy -/

/-- Conjugacy at concrete different exposures: prior `Gamma(3, 1)`, cells with exposures `1, 2`
and counts `0, 4` give the posterior `Gamma(7, 4)`. -/
example (r : ℝ) :
    (∏ i : Fin 2, poissonExposureLik (![1, 2] i) (![0, 4] i) r) * gammaPDFReal 3 1 r /
        (∫ x, ∏ i : Fin 2, poissonExposureLik (![1, 2] i) (![0, 4] i) x ∂gammaMeasure 3 1) =
      gammaPDFReal 7 4 r := by
  rw [pooledPosterior_eq_gammaPDFReal (by norm_num) (by norm_num)
    (fun i => by fin_cases i <;> norm_num)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- With a single cell the pooled posterior is the one-cell posterior of
`HierarchicalCount.posterior_eq_gammaPDFReal`. -/
example {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (k : ℕ) (r : ℝ) :
    (∏ _i : Unit, poissonExposureLik s k r) * gammaPDFReal a b r /
        (∫ x, ∏ _i : Unit, poissonExposureLik s k x ∂gammaMeasure a b) =
      poissonExposureLik s k r * gammaPDFReal a b r / marginalLik a b s k := by
  rw [pooledPosterior_eq_gammaPDFReal (s := fun _ => s) (k := fun _ => k) ha hb (fun _ => hs),
    posterior_eq_gammaPDFReal ha hb hs]
  simp

/-- With no cells the pooled posterior is the prior `Gamma(a, b)`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Empty → ℝ) (k : Empty → ℕ) (r : ℝ) :
    (∏ i, poissonExposureLik (s i) (k i) r) * gammaPDFReal a b r /
        (∫ x, ∏ i, poissonExposureLik (s i) (k i) x ∂gammaMeasure a b) = gammaPDFReal a b r := by
  simpa using pooledPosterior_eq_gammaPDFReal ha hb (s := s) (fun i => i.elim) k r

/-! ### Deterministic consistency -/

/-- The hypotheses of the deterministic core are satisfiable: exposure `S n = n` and count
`K n = 2 n`, so `K / S = 2` for `n ≥ 1` (checked from the values, not the theorem). The posterior
mean `(a + 2n) / (b + n)` then tends to `2` and the posterior concentrates at `2`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => posteriorMean a b n (2 * n)) atTop (𝓝 2) ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => gammaMeasure (a + ((2 * n : ℕ) : ℝ)) (b + n)
        {x | ε ≤ |x - 2|}) atTop (𝓝 0) := by
  have hK : Tendsto (fun n : ℕ => (((2 * n : ℕ) : ℝ)) / (n : ℝ)) atTop (𝓝 2) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  obtain ⟨h1, -, h3⟩ := tendsto_pooledPosterior_of_tendsto ha hb tendsto_natCast_atTop_atTop hK
  exact ⟨h1, h3⟩

/-- The posterior mean in the example above, from the definition: `(a + 2n) / (b + n)`. -/
example (a b : ℝ) (n : ℕ) : posteriorMean a b n (2 * n) = (a + 2 * n) / (b + n) := by
  simp [posteriorMean]

/-! ### Almost-sure consistency on a product space of Poisson counts -/

/-- Exposures alternating between `1` and `2`: genuinely different across cells. -/
noncomputable def altExposure (i : ℕ) : ℝ≥0 := 1 + ((i % 2 : ℕ) : ℝ≥0)

/-- The alternating exposures are bounded by `2`. -/
lemma altExposure_le (i : ℕ) : (altExposure i : ℝ) ≤ 2 := by
  have : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have : ((i % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 this
  simp only [altExposure, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast]
  linarith

/-- The total alternating exposure diverges (it is at least `n`). -/
lemma tendsto_sum_altExposure :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (altExposure i : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  calc (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.range n, (altExposure i : ℝ) := Finset.sum_le_sum fun i _ => by
        simp [altExposure]

/-- **Non-vacuity of `ae_tendsto_pooledPosterior_poisson`.** On the product space of independent
counts `Xᵢ ∼ Po(sᵢ r₀)` with the alternating exposures `sᵢ ∈ {1, 2}`, the pooled posterior mean
tends to `r₀` almost surely. -/
lemma ae_tendsto_altExposure (r₀ : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂(Measure.infinitePi fun i : ℕ => poissonMeasure (altExposure i * r₀)),
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, (altExposure i : ℝ))
        (∑ i ∈ Finset.range n, ω i)) atTop (𝓝 r₀) := by
  have hind := iIndepFun_infinitePi (P := fun i : ℕ => poissonMeasure (altExposure i * r₀))
    (X := fun _ => id) (fun _ => measurable_id)
  have h := ae_tendsto_pooledPosterior_poisson (X := fun i (ω : ℕ → ℕ) => ω i) (r₀ := r₀)
    ha hb altExposure_le tendsto_sum_altExposure
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩)
    (fun i j hij => hind.indepFun hij)
  filter_upwards [h] with ω hω
  exact hω.1

/-- The boundary rate `r₀ = 0`: every count is `Po(0) = δ₀`, and the posterior mean still tends
to `0`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂(Measure.infinitePi fun i : ℕ => poissonMeasure (altExposure i * 0)),
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, (altExposure i : ℝ))
        (∑ i ∈ Finset.range n, ω i)) atTop (𝓝 0) := by
  simpa using ae_tendsto_altExposure 0 ha hb

/-- A positive rate `r₀ = 3`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂(Measure.infinitePi fun i : ℕ => poissonMeasure (altExposure i * 3)),
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, (altExposure i : ℝ))
        (∑ i ∈ Finset.range n, ω i)) atTop (𝓝 3) := by
  simpa using ae_tendsto_altExposure 3 ha hb

end MathlibExtTest.Biology.Omics.HierarchicalCountExposures
