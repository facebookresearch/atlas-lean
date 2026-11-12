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

end MathlibExtTest.Probability.Statistics.SampleLaw
