/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SampleLaw
public import MathlibExt.Probability.Distributions.CochranIndependence
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics

namespace MathlibExtTest.Probability.Statistics.SampleLaw

/-- `n = 1`: the one-coordinate sample law projects back to `ν`. -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin 1 => ν).map (fun x => x 0) = ν := by
  exact (measurePreserving_eval (fun _ : Fin 1 => ν) 0).map_eq

/-- `n = 0`: the empty sample law is a Dirac mass (no normalized average is claimed). -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    Measure.pi (fun _ : Fin 0 => ν) = Measure.dirac (fun i => Fin.elim0 i) := by
  exact Measure.pi_of_empty _ _

/-- Converse, generic use: a tuple with law `νⁿ` has independent coordinates, each with law
`ν`; `iIndepFun_and_hasLaw_of_hasLaw_tuple_pi` returns both conclusions. -/
example {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν] {n : ℕ}
    {X : Fin n → Ω → S} (h : HasLaw (fun ω i => X i ω) (Measure.pi fun _ : Fin n => ν) μ) :
    iIndepFun X μ ∧ ∀ i, HasLaw (X i) ν μ :=
  ⟨(iIndepFun_and_hasLaw_of_hasLaw_tuple_pi h).1,
    fun i => (iIndepFun_and_hasLaw_of_hasLaw_tuple_pi h).2 i⟩

/-- Converse on the canonical model: the coordinate projections of the product space
`(Fin n → S, νⁿ)` are independent with law `ν`, from `HasLaw.id` for the identity tuple. -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) :
    iIndepFun (fun (i : Fin n) (ω : Fin n → S) => ω i) (Measure.pi fun _ : Fin n => ν) ∧
      ∀ i : Fin n, HasLaw (fun ω : Fin n → S => ω i) ν (Measure.pi fun _ : Fin n => ν) :=
  iIndepFun_and_hasLaw_of_hasLaw_tuple_pi (X := fun i (ω : Fin n → S) => ω i) HasLaw.id

/-- Converse, boundary `n = 1`: the single coordinate of `(Fin 1 → S, ν¹)` has law `ν`. -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    HasLaw (fun ω : Fin 1 → S => ω 0) ν (Measure.pi fun _ : Fin 1 => ν) :=
  (iIndepFun_and_hasLaw_of_hasLaw_tuple_pi (X := fun i (ω : Fin 1 → S) => ω i) HasLaw.id).2 0

/-- Converse, boundary `n = 0`: the empty family on `(Fin 0 → S, ν⁰)` is independent (and the
marginal statement is vacuous). -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    iIndepFun (fun (i : Fin 0) (ω : Fin 0 → S) => ω i) (Measure.pi fun _ : Fin 0 => ν) :=
  (iIndepFun_and_hasLaw_of_hasLaw_tuple_pi (X := fun i (ω : Fin 0 → S) => ω i) HasLaw.id).1

/-- Negative check: two coordinates equal to the same fair coin have the right marginals but
are not independent, so `iIndepFun.hasLaw_pi` cannot be applied to them. -/
example : ¬ iIndepFun (fun _ : Fin 2 => (id : Bool → Bool))
    ((2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)) := by
  intro h
  have key := (h.indepFun (i := 0) (j := 1) (by decide)).measure_inter_preimage_eq_mul
    {true} {false} (measurableSet_singleton _) (measurableSet_singleton _)
  simp at key

/-- **Use test: Gaussian sample mean.** For independent `Xᵢ ~ N(μ₀, v)`, `i : Fin n`, `n ≥ 1`,
`hasLaw_statistic` with the statistic `x ↦ (∑ i, x i) / n` and the Atlas theorem
`ProbabilityTheory.hasLaw_sampleMean` (provided) give `X̄ ~ N(μ₀, v / n)`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 0 < n) (μ₀ : ℝ) (v : NNReal) {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal μ₀ v) μ) (hind : iIndepFun X μ) :
    HasLaw (fun ω => (∑ i, X i ω) / n) (gaussianReal μ₀ (v / n)) μ := by
  have h := hasLaw_statistic hlaw hind (T := fun x : Fin n → ℝ => (∑ i, x i) / n) (by fun_prop)
  rwa [(hasLaw_sampleMean hn μ₀ v).map_eq] at h

/-- A fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The sign `±1` of a coin toss. -/
noncomputable def coinSign (b : Bool) : ℝ := if b then 1 else -1

/-- Positive: a constant integrand integrates to itself. -/
example (c : ℝ) {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → S}
    (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hg : Integrable (fun _ => c) ν) :
    ∫ ω, (∑ _ : Fin n, c) / (n : ℝ) ∂μ = c := by
  have h := MathlibExt.Probability.Statistics.integral_empiricalMean_of_common_marginals hn hg hlaw
  simpa [integral_const] using h

/-- Boundary: at `n = 1` the empirical average is the single observation. -/
example {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]
    {X : Fin 1 → Ω → S} {g : S → ℝ}
    (hlaw : ∀ i, HasLaw (X i) ν μ)
    (hg : Integrable g ν) :
    ∫ ω, (∑ i, g (X i ω)) / ((1 : ℕ) : ℝ) ∂μ = ∫ s, g s ∂ν := by
  exact MathlibExt.Probability.Statistics.integral_empiricalMean_of_common_marginals zero_lt_one hg hlaw

/-- Negative: the same draw twice is identically distributed but not independent, so the
tuple law is not the product law. -/
example : ¬ iIndepFun (fun _ : Fin 2 => coinSign) fairCoin := by
  intro h
  have h01 : IndepFun coinSign coinSign fairCoin :=
    h.indepFun (show (0 : Fin 2) ≠ 1 by decide)
  have hmeas : MeasurableSet ({1} : Set ℝ) := measurableSet_singleton 1
  have heq := h01.measure_inter_preimage_eq_mul _ _ hmeas hmeas
  have h1 : (-1 : ℝ) ≠ 1 := by norm_num
  have hpre : coinSign ⁻¹' ({1} : Set ℝ) = ({true} : Set Bool) := by
    ext b
    cases b <;> simp [coinSign, h1]
  rw [hpre, Set.inter_self] at heq
  have hval : fairCoin {true} = (2 : ENNReal)⁻¹ := by simp [fairCoin]
  rw [hval] at heq
  have hcon := congrArg ENNReal.toReal heq
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv] at hcon

/-- Non-vacuous `g = id` case: iid standard Gaussians average to expectation `0`. The
marginals come from the canonical product model via `Measure.pi_map_eval`;
integrability is `memLp_id_gaussianReal`. -/
example (n : ℕ) (hn : 0 < n) :
    ∫ ω, (∑ i : Fin n, ω i) / (n : ℝ) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 := by
  have hlaw : ∀ i : Fin n, HasLaw (fun ω : Fin n → ℝ => ω i) (gaussianReal 0 1)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, by
      have h := Measure.pi_map_eval (fun _ : Fin n => gaussianReal 0 1) i
      rw [show (fun ω : Fin n → ℝ => ω i) = Function.eval i from rfl, h]
      simp [measure_univ]⟩
  have hg : Integrable id (gaussianReal 0 1) := (memLp_id_gaussianReal 2).integrable one_le_two
  have hmain : (∫ ω, (∑ i : Fin n, ω i) / (n : ℝ)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) = ∫ s, id s ∂(gaussianReal 0 1) :=
    MathlibExt.Probability.Statistics.integral_empiricalMean_of_common_marginals hn hg hlaw
  have hval : (∫ s, id s ∂(gaussianReal (0 : ℝ) (1 : NNReal))) = 0 := integral_id_gaussianReal
  exact hmain.trans hval

/-- Non-vacuity: a nonconstant bounded `g` on a Bernoulli(1/2) law gives a nontrivial
numeric check. With `n` independent fair coins and `g` the success indicator, the
empirical average has expectation `1 / 2`. -/
example (n : ℕ) (hn : 0 < n) :
    ∫ ω, (∑ i : Fin n, (if ω i then (1 : ℝ) else 0)) / (n : ℝ)
      ∂(Measure.pi fun _ : Fin n => fairCoin) = 1 / 2 := by
  have hlaw : ∀ i : Fin n, HasLaw (fun ω : Fin n → Bool => ω i) fairCoin
      (Measure.pi fun _ : Fin n => fairCoin) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, by
      have h := Measure.pi_map_eval (fun _ : Fin n => fairCoin) i
      rw [show (fun ω : Fin n → Bool => ω i) = Function.eval i from rfl, h]
      simp only [measure_univ, Finset.prod_const_one, one_smul]⟩
  have hg : Integrable (fun b : Bool => if b then (1 : ℝ) else 0) fairCoin :=
    Integrable.of_finite
  have hmain : (∫ ω, (∑ i : Fin n, (if ω i then (1 : ℝ) else 0)) / (n : ℝ)
      ∂(Measure.pi fun _ : Fin n => fairCoin))
      = ∫ b, (if b then (1 : ℝ) else 0) ∂fairCoin :=
    MathlibExt.Probability.Statistics.integral_empiricalMean_of_common_marginals hn hg hlaw
  have hval : (∫ b, (if b then (1 : ℝ) else 0) ∂fairCoin) = 1 / 2 := by
    rw [fairCoin, integral_smul_measure,
      integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_dirac, integral_dirac]
    simp [ENNReal.toReal_inv]
  exact hmain.trans hval

end MathlibExtTest.Probability.Statistics.SampleLaw
