/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.StdGaussianHyperplane

/-!
# Sheppard's formula

For a standard bivariate normal vector with correlation `ρ ∈ (-1, 1)`, the open first quadrant
has probability `1/4 + arcsin ρ / (2π)` (W. F. Sheppard, *Phil. Trans. R. Soc. Lond. A* 192
(1899), 101–167; Y. L. Tong, *The Multivariate Normal Distribution*, Springer, 1990, Ch. 3).

The proof realises Mathlib's `multivariateGaussian 0 S` as the law of `(⟪u, r⟫, ⟪v, r⟫)` for a
standard Gaussian `r` in the plane and unit vectors with `⟪u, v⟫ = ρ` (by characteristic
functions), and applies `StdGaussianHyperplane.stdGaussian_pos_pos`, which rests on the
random-hyperplane computation of Goemans and Williamson (*J. ACM* 42(6) (1995), Lemma 3.2).
-/

@[expose] public section

namespace MathlibExt.Probability.Distributions.SheppardArcsine

open Real MeasureTheory ProbabilityTheory Set Matrix
  MathlibExt.Probability.Distributions.StdGaussianHyperplane

/-- **Sheppard's formula (Gaussian arcsine law).** For `ρ ∈ (-1, 1)`, let `γ` be the Gaussian
measure on `ℝ²` with mean `0` and covariance matrix with unit diagonal and off-diagonal
entries `ρ`. Then the open first quadrant has `γ`-probability `1/4 + arcsin ρ / (2π)`
(W. F. Sheppard, "On the application of the theory of error to cases of normal distribution and
normal correlation", *Phil. Trans. R. Soc. Lond. A* 192 (1899), 101–167; Y. L. Tong, *The
Multivariate Normal Distribution*, Springer, 1990, Ch. 3). -/
theorem sheppard_quadrant_probability_arcsine (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1) 1) :
    let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of (fun i j => if i = j then 1 else ρ);
    (ProbabilityTheory.multivariateGaussian 0 S).real {x | 0 < x 0 ∧ 0 < x 1}
      = 1 / 4 + Real.arcsin ρ / (2 * Real.pi) := by
  intro S
  obtain ⟨h1, h2⟩ := hρ
  set s := √(1 - ρ ^ 2) with hs
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  set e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  set e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have ho := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 2)
  have h00 : inner ℝ e₀ e₀ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, ho.1 0, one_pow]
  have h11 : inner ℝ e₁ e₁ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, ho.1 1, one_pow]
  have h01 : inner ℝ e₀ e₁ = (0 : ℝ) := ho.2 (by decide)
  have h10 : inner ℝ e₁ e₀ = (0 : ℝ) := by rw [real_inner_comm, h01]
  set u := e₀ with hu
  set v := ρ • e₀ + s • e₁ with hv
  have huv : inner ℝ u v = ρ := by
    rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right, h00, h01]; ring
  have hvv : inner ℝ v v = (1 : ℝ) := by
    rw [hv, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, h00, h01, h10, h11]
    nlinarith
  have hnu : ‖u‖ = 1 := ho.1 0
  have hnv : ‖v‖ = 1 := by
    have h := hvv
    rw [real_inner_self_eq_norm_sq] at h
    have := norm_nonneg v
    nlinarith [sq_nonneg (‖v‖ - 1)]
  -- the map to the plane
  let Φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun r => WithLp.toLp 2 ![inner ℝ u r, inner ℝ v r]
  have hΦc : Continuous Φ :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by fin_cases i <;> fun_prop)
  have hSpsd : S.PosSemidef := by
    have : S = Matrix.gram ℝ ![u, v] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [S, Matrix.gram_apply, hnu, hnv, huv, real_inner_comm]
    rw [this]
    exact Matrix.posSemidef_gram ℝ _
  have hlaw : multivariateGaussian 0 S = (stdGaussian (EuclideanSpace ℝ (Fin 2))).map Φ := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_multivariateGaussian hSpsd, charFun_map_inner_pair]
    congr 1
    have hn : ‖t 0 • u + t 1 • v‖ ^ 2 = t 0 ^ 2 + 2 * ρ * (t 0 * t 1) + t 1 ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        huv, hnu, hnv, Real.norm_eq_abs, Real.norm_eq_abs]
      ring_nf
      rw [sq_abs, sq_abs]
      ring
    have hq : t ⬝ᵥ S *ᵥ t = t 0 ^ 2 + 2 * ρ * (t 0 * t 1) + t 1 ^ 2 := by
      simp [S, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    rw [hq, ← Complex.ofReal_pow, hn]
    push_cast
    ring
  have hset : Φ ⁻¹' {x | 0 < x 0 ∧ 0 < x 1} = {r | 0 < inner ℝ u r ∧ 0 < inner ℝ v r} := by
    ext r
    simp [Φ]
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0 ∧ 0 < x 1} := by
    have hc : ∀ i : Fin 2, Continuous fun x : EuclideanSpace ℝ (Fin 2) => x i := fun i =>
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    rw [Set.ofPred_and]
    exact ((isOpen_lt continuous_const (hc 0)).inter
      (isOpen_lt continuous_const (hc 1))).measurableSet
  rw [hlaw, map_measureReal_apply hΦc.measurable hmeas, hset, stdGaussian_pos_pos hnu hnv, huv]

end MathlibExt.Probability.Distributions.SheppardArcsine
