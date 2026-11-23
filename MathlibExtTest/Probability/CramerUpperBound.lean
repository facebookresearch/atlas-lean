/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerUpperBound
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Tests: fixed-direction Chernoff bounds

Signature restatements of the three theorems in
`MathlibExt.Probability.CramerUpperBound`, plus a concrete application to the
i.i.d. Rademacher sequence (fair ±1 coin flips) on the infinite product space:
the probability that the empirical mean of `n` flips exceeds `1/2` is at most
`exp(-n * (1/2 - log (mgf of one flip at 1)))`. Numerically the rate is
`1/2 - log(cosh 1) ≈ 0.067 > 0`, so this is a genuine exponential decay bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.CramerUpperBound

namespace MathlibExtTest.Probability.CramerUpperBound

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Signature restatement: the one-dimensional Chernoff bound for the empirical
mean. -/
theorem measure_empiricalMean_le_of_threshold_test {X : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {t a : ℝ} (hInt : Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
    {n : ℕ} (hn : 0 < n) {E : Set Ω}
    (hEthr : ∀ ω ∈ E, a ≤ t * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω)
      - Real.log (mgf (X 0) μ t)) :
    (μ E).toReal ≤ Real.exp (-(n : ℝ) * a) :=
  measure_empiricalMean_le_of_threshold hXmeas hXindep hXident hInt hn hEthr

/-- Signature restatement: the fixed-direction Chernoff bound for i.i.d. vectors. -/
theorem cramer_upper_bound_test {d : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    {ξ : EuclideanSpace ℝ (Fin d)} {a : ℝ}
    (hInt : Integrable (fun ω => Real.exp ⟪ξ, X 0 ω⟫_ℝ) μ)
    (ha : ∀ x ∈ F, a ≤ ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) (n : ℕ) :
    ((empiricalMeanMeasureVec X μ n) F).toReal ≤ Real.exp (-(n : ℝ) * a) :=
  cramer_upper_bound hXmeas hXindep hXident hF hInt ha n

/-- Signature restatement: the fixed-direction Chernoff bound in rate form. -/
theorem cramer_upper_bound_rate_test {d : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    {ξ : EuclideanSpace ℝ (Fin d)}
    (hInt : Integrable (fun ω => Real.exp ⟪ξ, X 0 ω⟫_ℝ) μ)
    (hBdd : BddBelow ((fun x => ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) '' F)) :
    limsup (fun n : ℕ => ((empiricalMeanMeasureVec X μ n) F).toReal ^ (1 / (n : ℝ)))
        atTop ≤
      Real.exp (-sInf ((fun x => ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) '' F)) :=
  cramer_upper_bound_rate hXmeas hXindep hXident hF hInt hBdd

/-- The Rademacher law: fair ±1 coin flip, i.e. mass `1/2` at `-1` and `1/2`
at `1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (-1) 1 (⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩ : unitInterval)

/-- The Rademacher law is a probability measure. -/
instance : IsProbabilityMeasure rademacherMeasure := by
  show IsProbabilityMeasure
    (bernoulliMeasure (-1) 1 (⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩ : unitInterval))
  infer_instance

/-- The product measure on `ℕ → ℝ` with every coordinate Rademacher: the
canonical space of an i.i.d. fair ±1 sequence. -/
noncomputable def rademacherSeqMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => rademacherMeasure)

/-- The product Rademacher measure is a probability measure. -/
instance : IsProbabilityMeasure rademacherSeqMeasure := by
  show IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => rademacherMeasure))
  infer_instance

/-- The coordinate flips are independent. -/
theorem rademacher_iIndep :
    iIndepFun (fun i (ω : ℕ → ℝ) => ω i) rademacherSeqMeasure :=
  iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)

/-- The coordinate flips are identically distributed. -/
theorem rademacher_identDistrib (i : ℕ) :
    IdentDistrib (fun (ω : ℕ → ℝ) => ω i) (fun (ω : ℕ → ℝ) => ω 0)
      rademacherSeqMeasure rademacherSeqMeasure := by
  refine ⟨?_, ?_, ?_⟩
  · exact (measurable_pi_apply i).aemeasurable
  · exact (measurable_pi_apply 0).aemeasurable
  · show (Measure.infinitePi (fun _ : ℕ => rademacherMeasure)).map (Function.eval i)
      = (Measure.infinitePi (fun _ : ℕ => rademacherMeasure)).map (Function.eval 0)
    rw [MeasureTheory.Measure.infinitePi_map_eval, MeasureTheory.Measure.infinitePi_map_eval]

/-- Each flip is measurable. -/
theorem rademacher_measurable (i : ℕ) :
    Measurable (fun (ω : ℕ → ℝ) => ω i) :=
  measurable_pi_apply i

/-- A Rademacher flip takes values in `{-1, 1}` almost surely. -/
theorem rademacher_ae_mem : ∀ᵐ x ∂rademacherMeasure, x ∈ ({-1, 1} : Set ℝ) := by
  rw [ae_iff]
  show rademacherMeasure (({-1, 1} : Set ℝ)ᶜ) = 0
  show bernoulliMeasure (-1) 1 (⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩ : unitInterval)
    (({-1, 1} : Set ℝ)ᶜ) = 0
  rw [bernoulliMeasure_apply]
  · simp
  · exact ((measurableSet_singleton (1 : ℝ)).insert (-1)).compl

/-- The exponential moment `E[exp(ω₀)]` of one Rademacher flip is integrable. -/
theorem rademacher_integrable_exp :
    Integrable (fun (ω : ℕ → ℝ) => Real.exp (1 * ω 0)) rademacherSeqMeasure := by
  have hIntν : Integrable (fun x : ℝ => Real.exp (1 * x)) rademacherMeasure := by
    apply Integrable.mono' (integrable_const (Real.exp 1)) ?_ ?_
    · exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (1 * x))).aestronglyMeasurable
    · filter_upwards [rademacher_ae_mem] with x hx
      have hx1 : x ≤ 1 := by
        rcases hx with rfl | rfl <;> norm_num
      calc ‖Real.exp (1 * x)‖ = Real.exp (1 * x) := by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => rademacherMeasure) 0).integrable_comp_of_integrable
    hIntν

/-- **Cramér's upper bound for fair coin flips.** The probability that the
empirical mean of `n` fair ±1 flips is at least `1/2` decays exponentially in
`n` at rate `1/2 - log (mgf of one flip at 1)`. -/
theorem rademacher_empiricalMean_le {n : ℕ} (hn : 0 < n) :
    (rademacherSeqMeasure
      {ω : ℕ → ℝ | (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ω i ∈ Set.Ici (1 / 2 : ℝ)}).toReal
      ≤ Real.exp (-(n : ℝ) *
        ((1 / 2 : ℝ) - Real.log (mgf (fun (ω : ℕ → ℝ) => ω 0) rademacherSeqMeasure 1))) := by
  apply measure_empiricalMean_le_of_threshold (t := 1)
    (fun i => rademacher_measurable i) rademacher_iIndep rademacher_identDistrib
    rademacher_integrable_exp hn
  intro ω hω
  have havg : (1 / 2 : ℝ) ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ω i := hω
  linarith

#print axioms measure_empiricalMean_le_of_threshold
#print axioms cramer_upper_bound
#print axioms cramer_upper_bound_rate
#print axioms rademacher_empiricalMean_le

end MathlibExtTest.Probability.CramerUpperBound
