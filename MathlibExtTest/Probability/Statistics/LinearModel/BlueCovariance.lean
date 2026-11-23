/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.BlueCovariance
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.BlueCovariance` -/

namespace MathlibExtTest.LinearModelBlueCovariance

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- Intercept-only design: 3 observations, 1 regressor, all ones. -/
noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- First-observation estimator: picks out `y 0`. -/
noncomputable def A₀ : Matrix (Fin 1) (Fin 3) ℝ := !![1, 0, 0]

theorem AX₀ : A₀ * X₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  simp [A₀, X₀, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply]

theorem gram_X₀ : X₀ᵀ * X₀ = !![3] := by
  ext i j
  fin_cases i <;> fin_cases j
  simp [X₀, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.of_apply]

theorem ols_X₀ : olsMatrix X₀ = !![1 / 3, 1 / 3, 1 / 3] := by
  have hdet : (!![3] : Matrix (Fin 1) (Fin 1) ℝ).det = 3 :=
    Matrix.det_fin_one_of 3
  have hadj : (!![3] : Matrix (Fin 1) (Fin 1) ℝ).adjugate = !![1] := by
    rw [Matrix.adjugate_fin_one]
    ext i j
    fin_cases i <;> fin_cases j
    simp [Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply]
  have hinv : (!![3] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![(3 : ℝ)⁻¹] := by
    rw [Matrix.inv_def, hdet, hadj]
    ext i j
    fin_cases i <;> fin_cases j
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons]
  have h3 : (3 : ℝ)⁻¹ = 1 / 3 := by norm_num
  have hols : olsMatrix X₀ = (X₀ᵀ * X₀)⁻¹ * X₀ᵀ := olsMatrix_eq X₀
  rw [hols, gram_X₀, hinv, h3]
  ext i j
  fin_cases i <;> fin_cases j
  · show ((!![1/3] : Matrix (Fin 1) (Fin 1) ℝ) * X₀ᵀ) 0 0 = !![1/3,1/3,1/3] 0 0
    simp only [X₀, Matrix.mul_apply, Fin.sum_univ_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.transpose_apply, Matrix.of_apply, mul_one]
  · show ((!![1/3] : Matrix (Fin 1) (Fin 1) ℝ) * X₀ᵀ) 0 1 = !![1/3,1/3,1/3] 0 1
    simp only [X₀, Matrix.mul_apply, Fin.sum_univ_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.transpose_apply, Matrix.of_apply, mul_one]
  · show ((!![1/3] : Matrix (Fin 1) (Fin 1) ℝ) * X₀ᵀ) 0 2 = !![1/3,1/3,1/3] 0 2
    simp only [X₀, Matrix.mul_apply, Fin.sum_univ_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.transpose_apply, Matrix.of_apply, mul_one]

theorem diff_eq : A₀ * A₀ᵀ - olsMatrix X₀ * (olsMatrix X₀)ᵀ
    = Matrix.of fun _ _ => (2 : ℝ) / 3 := by
  rw [ols_X₀]
  ext i j
  fin_cases i <;> fin_cases j
  simp only [A₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply]
  norm_num

theorem posSemidef_diff :
    (A₀ * A₀ᵀ - olsMatrix X₀ * (olsMatrix X₀)ᵀ).PosSemidef := by
  rw [diff_eq]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    simp [Matrix.IsHermitian, Matrix.conjTranspose, Matrix.conjTranspose_apply,
      Matrix.transpose, Matrix.transpose_apply, Matrix.of_apply, star_trivial]
  · intro x
    have h_inner : ∀ xi : ℝ, x.sum (fun j xj => xi * (2/3 : ℝ) * xj)
        = xi * (2/3 : ℝ) * x 0 := by
      intro xi
      rw [Finsupp.sum_fintype x (fun j xj => xi * (2/3 : ℝ) * xj) (fun j => by simp),
        Fin.sum_univ_one]
    have h_outer : x.sum (fun i xi => xi * (2/3 : ℝ) * x 0)
        = x 0 * (2/3 : ℝ) * x 0 := by
      rw [Finsupp.sum_fintype x (fun i xi => xi * (2/3 : ℝ) * x 0) (fun i => by simp),
        Fin.sum_univ_one]
    simp only [Matrix.of_apply, star_trivial, h_inner, h_outer]
    have h_eq : x 0 * (2/3 : ℝ) * x 0 = (2/3 : ℝ) * (x 0) ^ 2 := by ring
    rw [h_eq]
    positivity

/-- The 8-point sample space: three independent fair bits. -/
abbrev Ω₀ := Fin 2 × Fin 2 × Fin 2

/-- Rademacher sign: `s₀ 0 = 1`, `s₀ 1 = -1`. -/
noncomputable def s₀ : Fin 2 → ℝ := ![1, -1]

/-- Error vector with independent Rademacher coordinates. -/
noncomputable def ε₀ : Ω₀ → Fin 3 → ℝ := fun ω => ![s₀ ω.1, s₀ ω.2.1, s₀ ω.2.2]

/-- Uniform probability measure: the average of the Dirac masses. -/
noncomputable def μ₀ : Measure Ω₀ := (8 : ENNReal)⁻¹ • ∑ ω : Ω₀, Measure.dirac ω

instance : IsProbabilityMeasure μ₀ := ⟨by
  unfold μ₀
  rw [Measure.smul_apply, Measure.finsetSum_apply Finset.univ _ _]
  simp [Fintype.card_prod, smul_eq_mul, ENNReal.inv_mul_cancel]⟩

/-- Integrals against `μ₀` are averages over the 8 points. -/
theorem integral_μ₀ (f : Ω₀ → ℝ) : ∫ ω, f ω ∂μ₀ = (∑ ω, f ω) / 8 := by
  unfold μ₀
  rw [integral_smul_measure, integral_finsetSum_measure (fun ω _ => integrable_dirac (by simp))]
  simp_rw [integral_dirac]
  show ((8 : ENNReal)⁻¹).toReal • (∑ ω, f ω) = (∑ ω, f ω) / 8
  have h8 : ((8 : ENNReal)⁻¹).toReal = (8 : ℝ)⁻¹ := by simp [ENNReal.toReal_inv]
  rw [h8, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem sum_ε₀ (i : Fin 3) : ∑ ω : Ω₀, ε₀ ω i = 0 := by
  fin_cases i <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, ε₀, s₀, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem sum_ε₀_mul (i j : Fin 3) :
    ∑ ω : Ω₀, ε₀ ω i * ε₀ ω j = (if i = j then 8 else 0 : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, ε₀, s₀, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num

theorem s₀_mem (x : Fin 2) : s₀ x = 1 ∨ s₀ x = -1 := by
  fin_cases x <;> simp [s₀, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem norm_ε₀_le (ω : Ω₀) (i : Fin 3) : ‖ε₀ ω i‖ ≤ 1 := by
  fin_cases i
  · simp [ε₀, Matrix.cons_val_zero]
    rcases s₀_mem ω.1 with h1 | h1 <;> rw [h1] <;> norm_num
  · simp [ε₀, Matrix.cons_val_one, Matrix.cons_val_zero]
    rcases s₀_mem ω.2.1 with h1 | h1 <;> rw [h1] <;> norm_num
  · simp [ε₀, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rcases s₀_mem ω.2.2 with h1 | h1 <;> rw [h1] <;> norm_num

theorem hint_ε₀ (i : Fin 3) : Integrable (fun ω => ε₀ ω i) μ₀ :=
  Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => norm_ε₀_le ω i)

theorem hmean_ε₀ (i : Fin 3) : ∫ ω, ε₀ ω i ∂μ₀ = 0 := by
  rw [integral_μ₀, sum_ε₀ i]
  norm_num

theorem hL2_ε₀ (i : Fin 3) : MemLp (fun ω => ε₀ ω i) 2 μ₀ :=
  MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => norm_ε₀_le ω i)

theorem hcov_ε₀ (i j : Fin 3) :
    cov[fun ω => ε₀ ω i, fun ω => ε₀ ω j; μ₀] = if i = j then (1 : ℝ) ^ 2 else 0 := by
  unfold covariance
  simp only [hmean_ε₀ i, hmean_ε₀ j, sub_zero]
  rw [integral_μ₀, sum_ε₀_mul i j]
  split_ifs <;> norm_num

theorem hX_X₀ : IsUnit (X₀ᵀ * X₀) := by
  rw [gram_X₀, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one_of]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

theorem hA₀_apply (w : Fin 3 → ℝ) : (A₀ *ᵥ w) 0 = w 0 := by
  simp [A₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply]

theorem hX₀_apply (β' : Fin 1 → ℝ) : (X₀ *ᵥ β') 0 = β' 0 := by
  simp [X₀, Matrix.mulVec, dotProduct, Matrix.of_apply]

/-- Integrability of a coordinate of `A *ᵥ (c + ε)`, from integrability of each
error coordinate. The constant vector `c` is typically `X *ᵥ β`.
(A copy of the private helper of the same name in `BlueCovariance`, which is not
visible from this file.) -/
private theorem integrable_mulVec_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {ε : Ω → m → ℝ} (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (A : Matrix k m ℝ) (a : k) (c : m → ℝ) :
    Integrable (fun ω => (A *ᵥ (c + ε ω)) a) μ := by
  have h_each : ∀ i : m, Integrable (fun ω => A a i * (c i + ε ω i)) μ := by
    intro i
    have h_const : Integrable (fun _ : Ω => A a i * c i) μ := integrable_const _
    have h_var : Integrable (fun ω => A a i * ε ω i) μ := by
      have h := (hint i).const_mul (A a i)
      simpa [smul_eq_mul] using h
    have h_eq : (fun ω => A a i * (c i + ε ω i))
        = (fun _ : Ω => A a i * c i) + (fun ω => A a i * ε ω i) := by
      ext ω
      simp [mul_add, Pi.add_apply]
    rw [h_eq]
    exact h_const.add h_var
  have h_sum : Integrable (fun ω => ∑ i, A a i * (c i + ε ω i)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => h_each i)
  have h_eq : (fun ω => (A *ᵥ (c + ε ω)) a)
      = (fun ω => ∑ i, A a i * (c i + ε ω i)) := by
    ext ω
    simp [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [h_eq]
  exact h_sum

theorem hunb_A₀ : ∀ β' : Fin 1 → ℝ, ∫ ω, A₀ *ᵥ (X₀ *ᵥ β' + ε₀ ω) ∂μ₀ = β' := by
  intro β'
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  rw [eval_integral (fun a => integrable_mulVec_apply hint_ε₀ A₀ a (X₀ *ᵥ β'))]
  simp_rw [hA₀_apply]
  simp_rw [Pi.add_apply, hX₀_apply]
  rw [integral_add (integrable_const _) (hint_ε₀ 0)]
  simp [integral_const, hmean_ε₀ 0]

/-- `A₀` against OLS on the `X₀` fixture: the `blue_covariance_minimality`
conclusion at `X := X₀`, `A := A₀`, `β := ![0]`, `σ := 1` over `(Ω₀, μ₀, ε₀)`.
This agrees with the `2 / 3` entry computed in `diff_eq`. -/
theorem blue_X₀ :
    ((Matrix.of fun a b => cov[fun ω => (A₀ *ᵥ (X₀ *ᵥ ![0] + ε₀ ω)) a,
        fun ω => (A₀ *ᵥ (X₀ *ᵥ ![0] + ε₀ ω)) b; μ₀])
      - (Matrix.of fun a b => cov[fun ω => (olsMatrix X₀ *ᵥ (X₀ *ᵥ ![0] + ε₀ ω)) a,
        fun ω => (olsMatrix X₀ *ᵥ (X₀ *ᵥ ![0] + ε₀ ω)) b; μ₀])).PosSemidef :=
  blue_covariance_minimality hX_X₀ ![0] 1 hL2_ε₀ hcov_ε₀ hint_ε₀ hmean_ε₀ A₀ hunb_A₀

end MathlibExtTest.LinearModelBlueCovariance
