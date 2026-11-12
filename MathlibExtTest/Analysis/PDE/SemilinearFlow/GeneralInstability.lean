/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.SemilinearFlow.GeneralInstability
import MathlibExt.Analysis.InnerProductSpace.BilateralShiftSpectrum

/-! Tests for linearized instability without an eigenvector.

* Beyond the eigenvector case: `L = 2 S` with `S` the bilateral shift on `ℓ²(ℤ, ℂ)` has `2` in
  its spectrum but **no eigenvector** (`twoShift_no_eigenvector`), so the eigenvector theorem
  `Instability.exists_escape_of_eigenvalue` cannot be applied; `exists_escape_of_mem_spectrum`
  applies and the origin is unstable for `y ↦ 2 S y`.
* Boundary case `‖z‖ = 1`: `1` is in the spectrum of `S`, but `S` is an isometry, so the origin
  is stable for `y ↦ S y`; the strict inequality `1 < ‖z‖` cannot be relaxed to `≤`.
* The frontier lemma produces approximate eigenvectors of `S` at `1`, a spectral value that is
  not an eigenvalue.
* The maximal-modulus lemma, the spectral-radius form and the flow form on `ℂ` with scalar
  linearizations; the approximate-eigenvalue form over `ℝ` with `G y = 2 y + y²`. -/

namespace MathlibExtTest.Analysis.PDE.SemilinearFlow.GeneralInstability

open MathlibExt.Analysis.PDE.SemilinearFlow.GeneralInstability
open MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator
open MathlibExt.Analysis.InnerProductSpace.BilateralShiftSpectrum
open scoped lp

/-- The bilateral shift on `ℓ²(ℤ, ℂ)`. -/
noncomputable abbrev S : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) := bilateralShiftCLM

/-! ### `2 S`: spectrum outside the unit disk, no eigenvector -/

theorem two_mem_spectrum_twoShift : (2 : ℂ) ∈ spectrum ℂ ((2 : ℂ) • S) := by
  have h := (spectrum.smul_mem_smul_iff (r := Units.mk0 (2 : ℂ) two_ne_zero) (s := (1 : ℂ))
    (a := S)).2 (mem_spectrum_bilateralShiftCLM_of_norm_eq_one (by simp))
  simpa [Units.smul_def] using h

/-- `2 S` has no eigenvector: `2 S x = ν x` forces `‖ν‖ = 2` and `|x n|` constant in `n ∈ ℤ`,
which is not square-summable unless `x = 0`. -/
theorem twoShift_no_eigenvector (ν : ℂ) (x : ℓ²(ℤ, ℂ)) (hx : ((2 : ℂ) • S) x = ν • x) :
    x = 0 := by
  by_contra hx0
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hν : ‖ν‖ = 2 := by
    have h := congrArg norm hx
    rw [smul_apply, norm_smul, norm_smul, norm_bilateralShiftCLM_apply]
      at h
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this] at h
    exact (mul_right_cancel₀ hxpos.ne' h).symm
  have hcoord : ∀ i : ℤ, ‖x i‖ = ‖x (i - 1)‖ := by
    intro i
    have h := congrArg (fun y : ℓ²(ℤ, ℂ) => y i) hx
    simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      bilateralShiftCLM_apply, bilateralShiftFun] at h
    have h2 := congrArg norm h
    rw [norm_mul, norm_mul, hν, show ‖(2 : ℂ)‖ = 2 by simp] at h2
    linarith
  have hconst : ∀ i : ℤ, ‖x i‖ = ‖x 0‖ := by
    intro i
    induction i using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [hcoord, add_sub_cancel_right, ih]
    | pred i ih => rw [← ih, hcoord (-(i : ℤ))]
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    exact hx0 (lp.ext (funext h))
  have hc : 0 < ‖x 0‖ := by rw [← hconst j]; exact norm_pos_iff.2 hj
  have hsum := (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have ht := hsum.tendsto_cofinite_zero
  simp only [hconst] at ht
  have := tendsto_nhds_unique ht tendsto_const_nhds
  have : 0 < ‖x 0‖ ^ (2 : ENNReal).toReal := by positivity
  linarith

/-- The origin is unstable for the linear map `y ↦ 2 S y` on `ℓ²(ℤ, ℂ)`, although `2 S` has no
eigenvector. -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : ℓ²(ℤ, ℂ), ‖x - 0‖ < δ ∧
    ∃ n, (∀ k < n, ‖(⇑((2 : ℂ) • S))^[k] x - 0‖ ≤ 1) ∧ ε ≤ ‖(⇑((2 : ℂ) • S))^[n] x - 0‖ :=
  exists_escape_of_mem_spectrum (C := 0) (p := 2) one_pos le_rfl one_lt_two
    (fun y _ => by simp) two_mem_spectrum_twoShift (by simp)

/-! ### Boundary `‖z‖ = 1`: the isometry `S` is stable -/

theorem norm_iterate_S (x : ℓ²(ℤ, ℂ)) (n : ℕ) : ‖(⇑S)^[n] x‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', norm_bilateralShiftCLM_apply, ih]

/-- `1 ∈ σ(S)` with `‖1‖ = 1`, yet no orbit of `S` escapes: the conclusion of
`exists_escape_of_mem_spectrum` fails, so `1 < ‖z‖` is needed. -/
example : (1 : ℂ) ∈ spectrum ℂ S ∧
    ¬ ∃ ε > 0, ∀ δ > 0, ∃ x : ℓ²(ℤ, ℂ), ‖x - 0‖ < δ ∧
      ∃ n, (∀ k < n, ‖(⇑S)^[k] x - 0‖ ≤ 1) ∧ ε ≤ ‖(⇑S)^[n] x - 0‖ := by
  refine ⟨mem_spectrum_bilateralShiftCLM_of_norm_eq_one (by simp), ?_⟩
  rintro ⟨ε, hε, h⟩
  obtain ⟨x, hx, n, -, hn⟩ := h ε hε
  rw [sub_zero, norm_iterate_S] at hn
  rw [sub_zero] at hx
  linarith

/-! ### Frontier lemma: approximate eigenvectors of `S` at `1` -/

/-- `1` is on the frontier of `σ(S) = {‖z‖ = 1}`, so `S` has approximate eigenvectors at `1`
(although `1` is not an eigenvalue). -/
example : ∀ κ > 0, ∃ v : ℓ²(ℤ, ℂ), ‖v‖ = 1 ∧ ‖S v - (1 : ℂ) • v‖ ≤ κ :=
  exists_approxEigenvector_of_mem_frontier (by
    rw [spectrum_bilateralShiftCLM, frontier_sphere' (0 : ℂ) 1]; simp)

/-! ### Scalar linearizations on `ℂ` -/

/-- Multiplication by `c` on `ℂ`, as an element of the algebra of operators. -/
noncomputable abbrev mulC (c : ℂ) : ℂ →L[ℂ] ℂ := algebraMap ℂ (ℂ →L[ℂ] ℂ) c

theorem mulC_apply (c y : ℂ) : mulC c y = c * y := by
  simp [mulC, Algebra.algebraMap_eq_smul_one]

theorem spectrum_mulC (c : ℂ) : spectrum ℂ (mulC c) = {c} := spectrum.scalar_eq c

theorem spectralRadius_mulC (c : ℂ) : spectralRadius ℂ (mulC c) = ‖c‖₊ := by
  rw [spectralRadius_eq_of_unital, spectrum_mulC]; simp

/-- Maximal-modulus lemma: `2` is on the frontier of `σ(2) = {2}`. -/
example : (2 : ℂ) ∈ frontier (spectrum ℂ (mulC 2)) :=
  mem_frontier_spectrum_of_nnnorm_eq_spectralRadius (by simp) two_ne_zero
    (spectralRadius_mulC 2)

/-- Spectral-radius form: `y ↦ 2 y + y²` on `ℂ` with `r(2) = 2 > 1`. -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : ℂ, ‖x - 0‖ < δ ∧
    ∃ n, (∀ k < n, ‖(fun y : ℂ => 2 * y + y ^ 2)^[k] x - 0‖ ≤ 1) ∧
      ε ≤ ‖(fun y : ℂ => 2 * y + y ^ 2)^[n] x - 0‖ := by
  refine exists_escape_of_one_lt_spectralRadius (L := mulC 2) (C := 1) (p := 2) one_pos
    zero_le_one one_lt_two (fun y _ => ?_) ?_
  · rw [mulC_apply, zero_add, sub_zero, show 2 * y + y ^ 2 - 2 * y = y ^ 2 by ring, one_mul,
      Real.rpow_two, norm_pow]
  · rw [spectralRadius_mulC]
    have : ‖(2 : ℂ)‖₊ = 2 := by ext; simp
    rw [this]; norm_num

/-- Flow form: `u' = u` on `ℂ`, `Φ t x = eᵗ x`, time-`1` map `e · x` with spectrum `{e}`. -/
example : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x : ℂ, ‖x - 0‖ < δ → ∀ t, 0 ≤ t →
    ‖(Real.exp t : ℂ) * x - 0‖ < ε := by
  refine not_lyapunovStable_of_timeMap_mem_spectrum (Φ := fun t x => (Real.exp t : ℂ) * x)
    (T := 1) (L := mulC (Real.exp 1)) (ρ := 1) (C := 0) (p := 2) (z := Real.exp 1)
    zero_le_one one_pos le_rfl one_lt_two (fun x => by simp) (fun n x _ => ?_) (fun y _ => ?_)
    (by simp) ?_
  · simp only [mul_one, Real.exp_add, Complex.ofReal_mul]; ring
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1)]
    exact Real.one_lt_exp_iff.2 one_pos

/-! ### Approximate-eigenvalue form over `ℝ`: `G y = 2 y + y²` -/

/-- Multiplication by `2` on `ℝ`. -/
noncomputable def L₂ : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

theorem L₂_apply (y : ℝ) : L₂ y = 2 * y := by simp [L₂]

theorem norm_L₂_pow_le (n : ℕ) : ‖L₂ ^ n‖ ≤ 1 * 2 ^ n := by
  have h : L₂ ^ n = (2 : ℝ) ^ n • ContinuousLinearMap.id ℝ ℝ := by
    rw [L₂, smul_pow, ← ContinuousLinearMap.one_def, one_pow]
  rw [h, one_mul]
  refine (norm_smul_le ((2 : ℝ) ^ n) (ContinuousLinearMap.id ℝ ℝ)).trans ?_
  rw [norm_pow, Real.norm_two]
  exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le

/-- The origin is unstable for `y ↦ 2 y + y²` on `ℝ`: `2` is an (exact, hence approximate)
eigenvalue of `L₂`, with `μ = 2 < 2² = 4`. -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ, ‖x - 0‖ < δ ∧
    ∃ n, (∀ k < n, ‖(fun y : ℝ => 2 * y + y ^ 2)^[k] x - 0‖ ≤ 1) ∧
      ε ≤ ‖(fun y : ℝ => 2 * y + y ^ 2)^[n] x - 0‖ := by
  refine exists_escape_of_approxEigenvalue (L := L₂) (ν := (2 : ℝ)) (p := 2) (M := 1)
    (μ := 2) one_pos zero_le_one one_lt_two (fun y _ => ?_) (fun κ hκ => ⟨1, by simp, ?_⟩)
    ?_ zero_le_two ?_ norm_L₂_pow_le
  · rw [L₂_apply, zero_add, sub_zero, show 2 * y + y ^ 2 - 2 * y = y ^ 2 by ring, one_mul,
      Real.rpow_two, norm_pow]
  · rw [L₂_apply, smul_eq_mul]; simpa using hκ.le
  · rw [Real.norm_two]; exact one_lt_two
  · rw [Real.norm_two, Real.rpow_two]; norm_num

end MathlibExtTest.Analysis.PDE.SemilinearFlow.GeneralInstability
