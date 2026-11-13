/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MonteCarloRate
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- `n = 1`: the sample mean of a single variable is the variable.
No probability-measure hypothesis is needed. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Fin 1 → Ω → ℝ} {mu : ℝ}
    (hInt : ∀ i, Integrable (X i) μ) (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu) :
    ∫ ω, (∑ i, X i ω) / (Fintype.card (Fin 1) : ℝ) ∂μ = mu :=
  MathlibExt.Probability.integral_sample_mean hInt hMean

/-- Degenerate variance: common variance `0` gives sample-mean
variance `0` for any `n`. No probability-measure hypothesis is needed. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ)
    (hIndep : iIndepFun (fun i => X i) μ)
    (hVar : ∀ i, variance (X i) μ = 0) :
    variance (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ)) μ = 0 := by
  have h := MathlibExt.Probability.variance_sample_mean (sigma2 := 0) hLp hIndep hVar
  simpa using h

-- Only the reference sample `X 0` needs to be square-integrable.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (n : ℕ) (hn : n ≠ 0) :
    variance (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) μ
      = variance (X 0) μ / (n : ℝ) := by
  exact MathlibExt.Probability.variance_sample_mean_of_iid X hIndep hIdent hMemLp n hn

/-! Test section (required): nondegenerate Gaussian-product witness with `n = 2`,
common variance `σ2 = 1`, so the conclusion `1 / 2` fails if the theorem returned
`σ2` instead of `σ2 / n`. -/

/-- Helper: the `i`-th coordinate law under the Gaussian product is `gaussianReal 0 1`. -/
private theorem coord_map_gaussian (i : Fin 2) :
    Measure.map (Function.eval i) (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))
      = gaussianReal 0 1 := by
  have h := Measure.pi_map_eval (fun _ : Fin 2 => gaussianReal 0 1) i
  simp only [measure_univ, Finset.prod_const_one, one_smul] at h
  exact h

/-- Test: coordinate projections are pairwise independent under the product measure. -/
example : Set.Pairwise (Finset.univ : Finset (Fin 2))
    fun i j => IndepFun (fun (ω : Fin 2 → ℝ) => ω i) (fun (ω : Fin 2 → ℝ) => ω j)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
  have hpi : iIndepFun (fun i (ω : Fin 2 → ℝ) => id (ω i))
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) :=
    iIndepFun_pi (μ := fun _ : Fin 2 => gaussianReal 0 1)
      (X := fun _ : Fin 2 => id) (fun i => aemeasurable_id)
  intro i _ j _ hij
  exact hpi.indepFun hij

/-- Test: coordinate projections are square-integrable under the product measure. -/
example (i : Fin 2) :
    MemLp (fun (ω : Fin 2 → ℝ) => ω i) 2
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
  have hmap := coord_map_gaussian i
  have hmem : MemLp id ((2 : NNReal) : ENNReal) (gaussianReal (0 : ℝ) (1 : NNReal)) :=
    memLp_id_gaussianReal 2
  have hcast : ((2 : NNReal) : ENNReal) = 2 := by norm_num
  rw [hcast] at hmem
  have hmp : MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) (gaussianReal 0 1) :=
    ⟨measurable_pi_apply i, hmap⟩
  have h := hmem.comp_measurePreserving hmp
  exact h

/-- Test: each coordinate projection has variance `1` under the product measure. -/
example (i : Fin 2) :
    ProbabilityTheory.variance (fun (ω : Fin 2 → ℝ) => ω i)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = 1 := by
  have hmap := coord_map_gaussian i
  have hae : AEMeasurable (Function.eval i)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) :=
    (measurable_pi_apply i).aemeasurable
  have hae_id : AEMeasurable id
      (Measure.map (Function.eval i)
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))) :=
    aemeasurable_id
  have h1 : ((1 : NNReal) : ℝ) = 1 := by norm_num
  have h := ProbabilityTheory.variance_map hae_id hae
  rw [hmap, ProbabilityTheory.variance_id_gaussianReal, h1] at h
  exact h.symm

/-- Test: the sample mean of two standard Gaussian coordinates has variance `1 / 2`. -/
example : ProbabilityTheory.variance
    (fun (ω : Fin 2 → ℝ) => (∑ i, ω i) / (Fintype.card (Fin 2) : ℝ))
    (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = 1 / 2 := by
  have hLp : ∀ i : Fin 2, MemLp (fun (ω : Fin 2 → ℝ) => ω i) 2
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
    intro i
    have hmap := coord_map_gaussian i
    have hmem : MemLp id ((2 : NNReal) : ENNReal)
        (gaussianReal (0 : ℝ) (1 : NNReal)) :=
      memLp_id_gaussianReal 2
    have hcast : ((2 : NNReal) : ENNReal) = 2 := by norm_num
    rw [hcast] at hmem
    have hmp : MeasurePreserving (Function.eval i)
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) (gaussianReal 0 1) :=
      ⟨measurable_pi_apply i, hmap⟩
    exact hmem.comp_measurePreserving hmp
  have hIndep : Set.Pairwise (Finset.univ : Finset (Fin 2))
      fun i j => IndepFun (fun (ω : Fin 2 → ℝ) => ω i) (fun (ω : Fin 2 → ℝ) => ω j)
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
    have hpi : iIndepFun (fun i (ω : Fin 2 → ℝ) => id (ω i))
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) :=
      iIndepFun_pi (μ := fun _ : Fin 2 => gaussianReal 0 1)
        (X := fun _ : Fin 2 => id) (fun i => aemeasurable_id)
    intro i _ j _ hij
    exact hpi.indepFun hij
  have hVar : ∀ i : Fin 2, ProbabilityTheory.variance (fun (ω : Fin 2 → ℝ) => ω i)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = 1 := by
    intro i
    have hmap := coord_map_gaussian i
    have hae : AEMeasurable (Function.eval i)
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) :=
      (measurable_pi_apply i).aemeasurable
    have hae_id : AEMeasurable id
        (Measure.map (Function.eval i)
          (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))) :=
      aemeasurable_id
    have h1 : ((1 : NNReal) : ℝ) = 1 := by norm_num
    have h := ProbabilityTheory.variance_map hae_id hae
    rw [hmap, ProbabilityTheory.variance_id_gaussianReal, h1] at h
    exact h.symm
  have h := MathlibExt.Probability.variance_sample_mean_of_pairwise
    (X := fun i (ω : Fin 2 → ℝ) => ω i) (sigma2 := (1 : ℝ)) hLp hIndep hVar
  rw [Fintype.card_fin] at h ⊢
  simp only [Nat.cast_ofNat] at h ⊢
  exact h
