/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ReducedForm
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Boundary tests for linear SEM reduced form and covariance

Two-equation chain, Gaussian nonvacuity for the SEM covariance (noise
only, and with a nonzero exogenous term `Γ Φ Γᵀ`), and a singular
two-cycle.

## References

- StataCorp (2017), Stata SEM Reference Manual Release 15,
  "methods and formulas for sem", "Model and parameterization".
- M. Drton (2016/2018), "Algebraic problems in structural equation
  modeling", arXiv:1612.05994, (2.1)-(2.2).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement.Test

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.Measurement
open scoped BigOperators Matrix ProbabilityTheory

/-- Two-equation chain `y1 = z1`, `y2 = b * y1 + z2`. -/
public def chainB (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; b, 0]

/-- Determinant of `I - chainB` is one. -/
public theorem chain_det (b : ℝ) : (1 - chainB b).det = 1 := by
  have h1 : (1 - chainB b) = !![1, 0; -b, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chainB]
  rw [h1, Matrix.det_fin_two_of]
  ring

/-- Inverse of `I - chainB` in closed form. -/
public theorem chain_inv (b : ℝ) : (1 - chainB b)⁻¹ = !![1, 0; b, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chainB, Matrix.mul_apply]

/-- Pushforward of diagonal noise through the chain inverse. -/
public theorem chain_cov (b ψ₁ ψ₂ : ℝ) :
  (1 - chainB b)⁻¹ * Matrix.diagonal ![ψ₁, ψ₂] * ((1 - chainB b)⁻¹)ᵀ =
    !![ψ₁, b * ψ₁; b * ψ₁, b ^ 2 * ψ₁ + ψ₂] := by
  rw [chain_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.vecMul_apply_eq_sum]
  all_goals ring

/-- Two-cycle with off-diagonal coefficients. -/
public def twoCycle (b₁₂ b₂₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, b₁₂; b₂₁, 0]

/-- Determinant of `I - twoCycle`. -/
public theorem twoCycle_det (b₁₂ b₂₁ : ℝ) :
  (1 - twoCycle b₁₂ b₂₁).det = 1 - b₁₂ * b₂₁ := by
  have h1 : (1 - twoCycle b₁₂ b₂₁) = !![1, -b₁₂; -b₂₁, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoCycle]
  rw [h1, Matrix.det_fin_two_of]
  ring

/-- A two-cycle with product one is singular. -/
public theorem twoCycle_singular :
  ¬ IsUnit (1 - twoCycle 2 (1 / 2)).det := by
  rw [twoCycle_det]
  have hzero : (1 : ℝ) - 2 * (1 / 2) = 0 := by norm_num
  rw [hzero]
  exact not_isUnit_zero

private theorem chain_memLp_fst :
  MemLp (fun ω : ℝ × ℝ => ω.1) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hmap : Measure.map Prod.fst
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
    simp
  have hid : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) :=
    ProbabilityTheory.memLp_id_gaussianReal' 2 (by decide)
  have hmem : MemLp (id : ℝ → ℝ) 2
    (Measure.map Prod.fst
      ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    rw [hmap]
    exact hid
  have hmeas : AEMeasurable (Prod.fst : ℝ × ℝ → ℝ)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurable_fst.aemeasurable
  have hcomp : MemLp (id ∘ Prod.fst) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hmem.comp_of_map hmeas
  simpa [Function.comp_def] using hcomp

private theorem chain_memLp_snd :
  MemLp (fun ω : ℝ × ℝ => ω.2) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hmap : Measure.map Prod.snd
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
    simp
  have hid : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) :=
    ProbabilityTheory.memLp_id_gaussianReal' 2 (by decide)
  have hmem : MemLp (id : ℝ → ℝ) 2
    (Measure.map Prod.snd
      ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    rw [hmap]
    exact hid
  have hmeas : AEMeasurable (Prod.snd : ℝ × ℝ → ℝ)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurable_snd.aemeasurable
  have hcomp : MemLp (id ∘ Prod.snd) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hmem.comp_of_map hmeas
  simpa [Function.comp_def] using hcomp

private theorem chain_var_fst :
  ProbabilityTheory.variance (fun ω : ℝ × ℝ => ω.1)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
  have hmap : Measure.map Prod.fst
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
    simp
  have hvar : ProbabilityTheory.variance (id : ℝ → ℝ)
    (gaussianReal 0 1) = 1 := by
    simp
  have hmeas : AEMeasurable (Prod.fst : ℝ × ℝ → ℝ)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurable_fst.aemeasurable
  have htrans := ProbabilityTheory.variance_map measurable_id.aemeasurable hmeas
  rw [hmap] at htrans
  have heq : (fun ω : ℝ × ℝ => ω.1) = id ∘ Prod.fst := rfl
  rw [heq, ← htrans]
  exact hvar

private theorem chain_var_snd :
  ProbabilityTheory.variance (fun ω : ℝ × ℝ => ω.2)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
  have hmap : Measure.map Prod.snd
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
    simp
  have hvar : ProbabilityTheory.variance (id : ℝ → ℝ)
    (gaussianReal 0 1) = 1 := by
    simp
  have hmeas : AEMeasurable (Prod.snd : ℝ × ℝ → ℝ)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurable_snd.aemeasurable
  have htrans := ProbabilityTheory.variance_map measurable_id.aemeasurable hmeas
  rw [hmap] at htrans
  have heq : (fun ω : ℝ × ℝ => ω.2) = id ∘ Prod.snd := rfl
  rw [heq, ← htrans]
  exact hvar

private theorem chain_cov_fst_snd :
  cov[fun ω : ℝ × ℝ => ω.1, fun ω : ℝ × ℝ => ω.2;
    (gaussianReal 0 1).prod (gaussianReal 0 1)] = 0 := by
  have hindep : ProbabilityTheory.IndepFun
    (fun ω : ℝ × ℝ => ω.1) (fun ω : ℝ × ℝ => ω.2)
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have h := ProbabilityTheory.indepFun_prod (μ := gaussianReal 0 1)
      (ν := gaussianReal 0 1)
      (measurable_id : Measurable (id : ℝ → ℝ))
      (measurable_id : Measurable (id : ℝ → ℝ))
    have e1 : (fun ω : ℝ × ℝ => id ω.1) = (fun ω : ℝ × ℝ => ω.1) := rfl
    have e2 : (fun ω : ℝ × ℝ => id ω.2) = (fun ω : ℝ × ℝ => ω.2) := rfl
    rw [e1, e2] at h
    exact h
  exact ProbabilityTheory.IndepFun.covariance_eq_zero hindep
    chain_memLp_fst chain_memLp_snd

/-- Constant zero exogenous input used in the chain model. -/
private def czero : (ℝ × ℝ) → Fin 1 → ℝ := fun _ _ => 0

/-- Nonvacuity: the chain with unit Gaussian noise attains its covariance. -/
public theorem chain_model_cov (b : ℝ) (i j : Fin 2) :
  cov[fun ω : ℝ × ℝ => ((1 - chainB b)⁻¹ *ᵥ ![ω.1, ω.2]) i,
    fun ω : ℝ × ℝ => ((1 - chainB b)⁻¹ *ᵥ ![ω.1, ω.2]) j;
    (gaussianReal 0 1).prod (gaussianReal 0 1)] =
    (!![1, b; b, b ^ 2 + 1] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have hdet : IsUnit (1 - chainB b).det := by
    rw [chain_det]
    exact isUnit_one
  have hstruct : ∀ ω : ℝ × ℝ, (1 - chainB b)⁻¹ *ᵥ ![ω.1, ω.2] =
    chainB b *ᵥ ((1 - chainB b)⁻¹ *ᵥ ![ω.1, ω.2]) +
      (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ czero ω +
      ![ω.1, ω.2] := by
    intro ω
    have hz : (0 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ czero ω = 0 :=
      Matrix.zero_mulVec _
    rw [hz, add_zero]
    exact (MathlibExt.Probability.Statistics.Measurement.eq_inv_mulVec_iff
      (chainB b) _ _ hdet).mpr rfl
  have hx : ∀ k : Fin 1, MemLp
    (fun ω : ℝ × ℝ => czero ω k) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    intro k
    have heq : (fun ω : ℝ × ℝ =>
      czero ω k) = fun _ => (0 : ℝ) := rfl
    rw [heq]
    exact MeasureTheory.memLp_const 0
  have hz0 : MemLp (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have heq : (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0) =
      fun ω : ℝ × ℝ => ω.1 := by
      funext ω
      simp
    rw [heq]
    exact chain_memLp_fst
  have hz1 : MemLp (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have heq : (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1) =
      fun ω : ℝ × ℝ => ω.2 := by
      funext ω
      simp
    rw [heq]
    exact chain_memLp_snd
  have hζ : ∀ k : Fin 2, MemLp
    (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) k) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    intro k
    fin_cases k
    · exact hz0
    · exact hz1
  have hΦ : ∀ k l : Fin 1,
    cov[fun ω : ℝ × ℝ => czero ω k,
      fun ω : ℝ × ℝ => czero ω l;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (0 : Matrix (Fin 1) (Fin 1) ℝ) k l := by
    intro k l
    have heq1 : (fun ω : ℝ × ℝ =>
      czero ω k) = fun _ => (0 : ℝ) := rfl
    have heq2 : (0 : Matrix (Fin 1) (Fin 1) ℝ) k l = 0 := by simp
    rw [heq1, heq2]
    simp only [ProbabilityTheory.covariance_const_left]
  have hΨ : ∀ k l : Fin 2,
    cov[fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) k,
      fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) l;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) k l := by
    have e0 : (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0) =
      fun ω : ℝ × ℝ => ω.1 := by
      funext ω
      simp
    have e1 : (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1) =
      fun ω : ℝ × ℝ => ω.2 := by
      funext ω
      simp
    have h00 : cov[fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0,
        fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0;
        (gaussianReal 0 1).prod (gaussianReal 0 1)] =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
      rw [e0, Matrix.one_apply_eq,
        ProbabilityTheory.covariance_self measurable_fst.aemeasurable,
        chain_var_fst]
    have h01 : cov[fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0,
        fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1;
        (gaussianReal 0 1).prod (gaussianReal 0 1)] =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
      rw [e0, e1, Matrix.one_apply_ne (by decide), chain_cov_fst_snd]
    have h10 : cov[fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1,
        fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 0;
        (gaussianReal 0 1).prod (gaussianReal 0 1)] =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
      rw [e1, e0, Matrix.one_apply_ne (by decide),
        ProbabilityTheory.covariance_comm, chain_cov_fst_snd]
    have h11 : cov[fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1,
        fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) 1;
        (gaussianReal 0 1).prod (gaussianReal 0 1)] =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
      rw [e1, Matrix.one_apply_eq,
        ProbabilityTheory.covariance_self measurable_snd.aemeasurable,
        chain_var_snd]
    intro k l
    fin_cases k <;> fin_cases l
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have hcross : ∀ k : Fin 1, ∀ l : Fin 2,
    cov[fun ω : ℝ × ℝ => czero ω k,
      fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ) l;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] = 0 := by
    intro k l
    have heq : (fun ω : ℝ × ℝ =>
      czero ω k) = fun _ => (0 : ℝ) := rfl
    rw [heq]
    simp only [ProbabilityTheory.covariance_const_left]
  have hmain := MathlibExt.Probability.Statistics.Measurement.covariance_structural
    (chainB b) (0 : Matrix (Fin 2) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (fun ω : ℝ × ℝ => (1 - chainB b)⁻¹ *ᵥ ![ω.1, ω.2])
    czero
    (fun ω : ℝ × ℝ => (![ω.1, ω.2] : Fin 2 → ℝ))
    hdet hstruct hx hζ hΦ hΨ hcross i j
  have hzero : (0 : Matrix (Fin 2) (Fin 1) ℝ) *
    (0 : Matrix (Fin 1) (Fin 1) ℝ) *
    (0 : Matrix (Fin 2) (Fin 1) ℝ)ᵀ + (1 : Matrix (Fin 2) (Fin 2) ℝ) =
    Matrix.diagonal ![1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hzero] at hmain
  have hchain := chain_cov b 1 1
  rw [hchain] at hmain
  simpa using hmain

/-- Loadings of one exogenous input on the chain: `y1 = g₁ x + z1`,
`y2 = b * y1 + g₂ x + z2`. -/
public def exoLoading (g₁ g₂ : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![g₁; g₂]

/-- The exogenous input `x = ω.1`. -/
public def exoInput (ω : ℝ × ℝ) : Fin 1 → ℝ := fun _ => ω.1

/-- The structural noise `ζ = (ω.2, 0)`, independent of the input. -/
public def exoNoise (ω : ℝ × ℝ) : Fin 2 → ℝ := ![ω.2, 0]

/-- Pushforward of `Γ Φ Γᵀ + Ψ` through the chain inverse, with the
`2 × 1` loading matrix, `Φ = 1` and `Ψ = diag(1, 0)`. -/
public theorem chain_exo_cov (b g₁ g₂ : ℝ) :
  (1 - chainB b)⁻¹ * (exoLoading g₁ g₂ * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
    (exoLoading g₁ g₂)ᵀ + !![1, 0; 0, 0]) * ((1 - chainB b)⁻¹)ᵀ =
    !![g₁ ^ 2 + 1, b * (g₁ ^ 2 + 1) + g₁ * g₂;
      b * (g₁ ^ 2 + 1) + g₁ * g₂,
      b ^ 2 * (g₁ ^ 2 + 1) + 2 * b * g₁ * g₂ + g₂ ^ 2] := by
  have hM : exoLoading g₁ g₂ * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (exoLoading g₁ g₂)ᵀ + !![1, 0; 0, 0] =
      !![g₁ ^ 2 + 1, g₁ * g₂; g₁ * g₂, g₂ ^ 2] := by
    rw [Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [exoLoading, Matrix.vecMul, dotProduct] <;> ring
  rw [hM, chain_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Nonvacuity with a nonzero exogenous term: for the chain driven by an
exogenous input `x` and noise `ζ`, independent standard Gaussians, the
covariance of `y` includes `Γ Φ Γᵀ` with `Γ = exoLoading g₁ g₂ ≠ 0` and
`Φ = 1`. Directly: `Var y1 = g₁² + 1`,
`Cov(y1, y2) = b (g₁² + 1) + g₁ g₂`, `Var y2 = (b g₁ + g₂)² + b²`. -/
public theorem chain_exo_model_cov (b g₁ g₂ : ℝ) (i j : Fin 2) :
  cov[fun ω : ℝ × ℝ =>
      ((1 - chainB b)⁻¹ *ᵥ (exoLoading g₁ g₂ *ᵥ exoInput ω + exoNoise ω)) i,
    fun ω : ℝ × ℝ =>
      ((1 - chainB b)⁻¹ *ᵥ (exoLoading g₁ g₂ *ᵥ exoInput ω + exoNoise ω)) j;
    (gaussianReal 0 1).prod (gaussianReal 0 1)] =
    (!![g₁ ^ 2 + 1, b * (g₁ ^ 2 + 1) + g₁ * g₂;
      b * (g₁ ^ 2 + 1) + g₁ * g₂,
      b ^ 2 * (g₁ ^ 2 + 1) + 2 * b * g₁ * g₂ + g₂ ^ 2] :
      Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have hdet : IsUnit (1 - chainB b).det := by
    rw [chain_det]
    exact isUnit_one
  have hstruct : ∀ ω : ℝ × ℝ,
    (1 - chainB b)⁻¹ *ᵥ (exoLoading g₁ g₂ *ᵥ exoInput ω + exoNoise ω) =
      chainB b *ᵥ ((1 - chainB b)⁻¹ *ᵥ
        (exoLoading g₁ g₂ *ᵥ exoInput ω + exoNoise ω)) +
        exoLoading g₁ g₂ *ᵥ exoInput ω + exoNoise ω := by
    intro ω
    rw [add_assoc]
    exact (MathlibExt.Probability.Statistics.Measurement.eq_inv_mulVec_iff
      (chainB b) _ _ hdet).mpr rfl
  have ex : ∀ k : Fin 1, (fun ω : ℝ × ℝ => exoInput ω k) =
    fun ω : ℝ × ℝ => ω.1 := fun _ => rfl
  have e0 : (fun ω : ℝ × ℝ => exoNoise ω 0) = fun ω : ℝ × ℝ => ω.2 := by
    funext ω
    simp [exoNoise]
  have e1 : (fun ω : ℝ × ℝ => exoNoise ω 1) = fun _ : ℝ × ℝ => (0 : ℝ) := by
    funext ω
    simp [exoNoise]
  have hx : ∀ k : Fin 1, MemLp (fun ω : ℝ × ℝ => exoInput ω k) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    intro k
    rw [ex k]
    exact chain_memLp_fst
  have hζ0 : MemLp (fun ω : ℝ × ℝ => exoNoise ω 0) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    rw [e0]
    exact chain_memLp_snd
  have hζ1 : MemLp (fun ω : ℝ × ℝ => exoNoise ω 1) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    rw [e1]
    exact MeasureTheory.memLp_const 0
  have hζ : ∀ k : Fin 2, MemLp (fun ω : ℝ × ℝ => exoNoise ω k) 2
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    intro k
    fin_cases k
    · exact hζ0
    · exact hζ1
  have hΦ : ∀ k l : Fin 1,
    cov[fun ω : ℝ × ℝ => exoInput ω k, fun ω : ℝ × ℝ => exoInput ω l;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) k l := by
    intro k l
    rw [Subsingleton.elim l k, ex k, Matrix.one_apply_eq,
      ProbabilityTheory.covariance_self measurable_fst.aemeasurable,
      chain_var_fst]
  have h00 : cov[fun ω : ℝ × ℝ => exoNoise ω 0, fun ω : ℝ × ℝ => exoNoise ω 0;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    rw [e0, ProbabilityTheory.covariance_self measurable_snd.aemeasurable,
      chain_var_snd]
    simp
  have h01 : cov[fun ω : ℝ × ℝ => exoNoise ω 0, fun ω : ℝ × ℝ => exoNoise ω 1;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [e1, ProbabilityTheory.covariance_const_right]
    simp
  have h10 : cov[fun ω : ℝ × ℝ => exoNoise ω 1, fun ω : ℝ × ℝ => exoNoise ω 0;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    rw [e1, ProbabilityTheory.covariance_const_left]
    simp
  have h11 : cov[fun ω : ℝ × ℝ => exoNoise ω 1, fun ω : ℝ × ℝ => exoNoise ω 1;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    rw [e1, ProbabilityTheory.covariance_const_left]
    simp
  have hΨ : ∀ k l : Fin 2,
    cov[fun ω : ℝ × ℝ => exoNoise ω k, fun ω : ℝ × ℝ => exoNoise ω l;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) k l := by
    intro k l
    fin_cases k <;> fin_cases l
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have c0 : cov[fun ω : ℝ × ℝ => ω.1, fun ω : ℝ × ℝ => exoNoise ω 0;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] = 0 := by
    rw [e0]
    exact chain_cov_fst_snd
  have c1 : cov[fun ω : ℝ × ℝ => ω.1, fun ω : ℝ × ℝ => exoNoise ω 1;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] = 0 := by
    rw [e1]
    exact ProbabilityTheory.covariance_const_right 0
  have hcross : ∀ k : Fin 1, ∀ l : Fin 2,
    cov[fun ω : ℝ × ℝ => exoInput ω k, fun ω : ℝ × ℝ => exoNoise ω l;
      (gaussianReal 0 1).prod (gaussianReal 0 1)] = 0 := by
    intro k l
    rw [ex k]
    fin_cases l
    · exact c0
    · exact c1
  have hmain := MathlibExt.Probability.Statistics.Measurement.covariance_structural
    (chainB b) (exoLoading g₁ g₂) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    (fun ω : ℝ × ℝ =>
      (1 - chainB b)⁻¹ *ᵥ (exoLoading g₁ g₂ *ᵥ exoInput ω + exoNoise ω))
    exoInput exoNoise hdet hstruct hx hζ hΦ hΨ hcross i j
  rw [chain_exo_cov] at hmain
  exact hmain

end MathlibExt.Probability.Statistics.Measurement.Test
