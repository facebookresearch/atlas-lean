/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Isotropic log-concave laws and thin-shell variance
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

import Mathlib.Analysis.Convex.Mul
import MathlibExt.Probability.BrownianQuadraticVariation
import MathlibExt.Probability.Distributions.GaussianDensity

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.ThinShell

/-- **Log-concave densities.** A function $f : \mathbb{R}^n \to \mathbb{R}$ is a log-concave
density when it is measurable, $f(x) \ge 0$ for every $x$, and
$f(x)^{1-t} f(y)^t \le f((1-t)x + ty)$ for all $x, y \in \mathbb{R}^n$ and every real $t$
with $0 < t < 1$.

No integrability or normalization of $f$ is required. -/
def IsLogConcaveDensity {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    ∀ x y : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, 0 < t → t < 1 →
      Real.rpow (f x) (1 - t) * Real.rpow (f y) t ≤ f ((1 - t) • x + t • y)

/-- **Isotropic log-concave probability measures.** A measure $\mu$ on $\mathbb{R}^n$ is
isotropic log-concave when it is a probability measure, it has density $f$ with respect to
Lebesgue measure for some log-concave density $f$, and for all coordinates $i, j$ the
functions $x \mapsto x_i$ and $x \mapsto x_i x_j$ are $\mu$-integrable with
$\int x_i \, d\mu(x) = 0$ and $\int x_i x_j \, d\mu(x) = \delta_{ij}$, that is, $1$ if $i = j$
and $0$ otherwise. -/
def IsIsotropicLogConcave {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsProbabilityMeasure μ ∧
    (∃ f : EuclideanSpace ℝ (Fin n) → ℝ, IsLogConcaveDensity f ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) ∧
    (∀ i : Fin n, Integrable (fun x => x i) μ ∧ (∫ x, x i ∂μ) = 0) ∧
    ∀ i j : Fin n, Integrable (fun x => x i * x j) μ ∧
      (∫ x, x i * x j ∂μ) = if i = j then 1 else 0

/-- **Normalized radius variance.** For a measure $\mu$ on $\mathbb{R}^n$, the normalized radius
variance of $\mu$ is $\frac{1}{n} \int (\|x\|^2 - n)^2 \, d\mu(x)$, computed in $[0, \infty]$,
where $\|x\|$ is the Euclidean norm (for $n = 0$ the integral is $0$ and so is the value).

When $\mu$ is a probability measure with $\int \|x\|^2 \, d\mu(x) = n$, as for an isotropic
one, this is the variance of $\|x\|^2$ divided by $n$. -/
noncomputable def normalizedRadiusVariance {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2) ∂μ) / (n : ℝ≥0∞)

/-- **Thin-shell variance constant.** Write $|x|$ for the Euclidean norm. The thin-shell
variance constant is the supremum, taken in $[0, \infty]$, of the normalized radius variance
$\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$ over all dimensions $n \ge 1$ and all isotropic
log-concave probability measures $\mu$ on $\mathbb{R}^n$. -/
noncomputable def thinShellVarianceConstant : ℝ≥0∞ :=
  sSup {v | ∃ n : ℕ, 0 < n ∧ ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
    IsIsotropicLogConcave μ ∧ normalizedRadiusVariance μ = v}

/-- **Thin-shell width.** Write $|x|$ for the Euclidean norm. For $n \in \mathbb{N}$, the
thin-shell width in dimension $n$ is the square root of the supremum, taken in $[0, \infty]$, of
$\int (|x| - \sqrt{n})^2 \, d\mu(x)$ over all isotropic log-concave probability measures $\mu$ on
$\mathbb{R}^n$, with $\sqrt{\infty} = \infty$. -/
noncomputable def thinShellWidth (n : ℕ) : ℝ≥0∞ :=
  ENNReal.rpow (sSup {v | ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
    IsIsotropicLogConcave μ ∧
      (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) = v}) (1 / 2)

/-- **Elementary radius deviation bound.** For all real numbers $r \ge 0$ and $d > 0$,
$(r - \sqrt{d})^2 \le (r^2 - d)^2 / d$. -/
theorem radius_deviation_sq_le {r d : ℝ} (hr : 0 ≤ r) (hd : 0 < d) :
    (r - Real.sqrt d) ^ 2 ≤ (r ^ 2 - d) ^ 2 / d := by
  have hs := Real.sqrt_nonneg d
  have hs2 := Real.sq_sqrt hd.le
  have hprod : 0 ≤ r * Real.sqrt d := by positivity
  have hsum : d ≤ (r + Real.sqrt d) ^ 2 := by nlinarith
  have hsq : 0 ≤ (r - Real.sqrt d) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hsq
  apply (le_div_iff₀ hd).2
  nlinarith [hmul]

/-- **Radius fluctuation is bounded by the normalized radius variance.** For every $n > 0$ and
every measure $\mu$ on $\mathbb{R}^n$, the integral $\int (\|x\| - \sqrt{n})^2 \, d\mu(x)$,
taken in $[0, \infty]$ with $\|x\|$ the Euclidean norm, is at most the normalized radius
variance of $\mu$.

The bound holds even when the moments are infinite. -/
theorem radius_fluctuation_le_normalized_variance {n : ℕ} (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) ≤
      normalizedRadiusVariance μ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hni : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    apply ENNReal.inv_ne_top.2
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2 / (n : ℝ)) ∂μ := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (radius_deviation_sq_le (norm_nonneg x) hnR)
    _ = (n : ℝ≥0∞)⁻¹ *
        (∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2) ∂μ) := by
      simp only [ENNReal.ofReal_div_of_pos hnR, ENNReal.ofReal_natCast]
      simpa only [div_eq_mul_inv, mul_comm] using
        lintegral_const_mul' (μ := μ) (n : ℝ≥0∞)⁻¹
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2)) hni
    _ = normalizedRadiusVariance μ := by
      simp only [normalizedRadiusVariance, div_eq_mul_inv, mul_comm]

/-- **The thin-shell variance constant bounds the normalized radius variance of isotropic
log-concave measures.** For every $n > 0$ and every isotropic log-concave probability measure
$\mu$ on $\mathbb{R}^n$, the normalized radius variance of $\mu$ is at most the thin-shell
variance constant. -/
theorem normalizedRadiusVariance_le_constant {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    normalizedRadiusVariance μ ≤ thinShellVarianceConstant := by
  exact le_sSup ⟨n, hn, μ, hμ, rfl⟩

/-- **Characterization of bounds on the thin-shell variance constant.** For every
$C \in [0, \infty]$, the thin-shell variance constant is at most $C$ if and only if, for every
$n > 0$ and every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$, the
normalized radius variance of $\mu$ is at most $C$. -/
theorem thinShellVarianceConstant_le_iff {C : ℝ≥0∞} :
    thinShellVarianceConstant ≤ C ↔
      ∀ n : ℕ, 0 < n → ∀ μ : Measure (EuclideanSpace ℝ (Fin n)),
        IsIsotropicLogConcave μ → normalizedRadiusVariance μ ≤ C := by
  constructor
  · intro h n hn μ hμ
    exact (normalizedRadiusVariance_le_constant hn hμ).trans h
  · intro h
    apply sSup_le
    rintro v ⟨n, hn, μ, hμ, rfl⟩
    exact h n hn μ hμ

/-- **The thin-shell variance constant bounds the radius fluctuation.** For every $n > 0$ and
every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$, the integral
$\int (\|x\| - \sqrt{n})^2 \, d\mu(x)$, taken in $[0, \infty]$ with $\|x\|$ the Euclidean
norm, is at most the thin-shell variance constant. -/
theorem radius_fluctuation_le_constant {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) ≤
      thinShellVarianceConstant := by
  exact (radius_fluctuation_le_normalized_variance hn μ).trans
    (normalizedRadiusVariance_le_constant hn hμ)

/-- **The thin-shell variance constant is nonnegative.** The thin-shell variance constant, a
value in $[0, \infty]$, is at least $0$. -/
theorem thinShellVarianceConstant_nonneg : 0 ≤ thinShellVarianceConstant :=
  bot_le

/-- **Thin-shell width is at most the square root of the variance constant.** For every
dimension $n \ge 1$, the thin-shell width in dimension $n$ is at most the square root of the
thin-shell variance constant, computed in $[0, \infty]$ with $\sqrt{\infty} = \infty$. -/
theorem thinShellWidth_le_sqrt_constant {n : ℕ} (hn : 0 < n) :
    thinShellWidth n ≤ ENNReal.rpow thinShellVarianceConstant (1 / 2) := by
  unfold thinShellWidth
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply sSup_le
  rintro v ⟨μ, hμ, rfl⟩
  exact radius_fluctuation_le_constant hn hμ

/-- **A uniform variance bound makes the thin-shell variance constant finite.** If $C$ is a real
number such that for every $n > 0$ and every isotropic log-concave probability measure $\mu$
on $\mathbb{R}^n$ the normalized radius variance of $\mu$ is at most $\max(C, 0)$, then the
thin-shell variance constant is finite. -/
theorem thinShellVarianceConstant_lt_top_of_bound {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ μ : Measure (EuclideanSpace ℝ (Fin n)),
      IsIsotropicLogConcave μ → normalizedRadiusVariance μ ≤ ENNReal.ofReal C) :
    thinShellVarianceConstant < ⊤ := by
  exact lt_of_le_of_lt (thinShellVarianceConstant_le_iff.mpr hC) ENNReal.ofReal_lt_top

section

open ProbabilityTheory WithLp
open scoped ProbabilityTheory

private theorem isLogConcaveDensity_stdGaussianPDFReal (n : ℕ) :
    IsLogConcaveDensity (MetaMathlibExt.stdGaussianPDFReal (ι := Fin n)) := by
  have hc : 0 < ((√(2 * Real.pi)) ^ Fintype.card (Fin n))⁻¹ := by positivity
  refine ⟨MetaMathlibExt.measurable_stdGaussianPDFReal,
    MetaMathlibExt.stdGaussianPDFReal_nonneg, ?_⟩
  intro x y t ht ht₁
  have hsq : ‖(1 - t) • x + t • y‖ ^ 2 ≤ (1 - t) * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    change ((1 - t) * x i + t * y i) ^ 2 ≤ (1 - t) * (x i) ^ 2 + t * (y i) ^ 2
    have hs : ConvexOn ℝ Set.univ (fun s : ℝ ↦ s ^ 2) := by
      exact (even_two : Even (2 : ℕ)).convexOn_pow
    exact hs.2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) (sub_nonneg.mpr ht₁.le) ht.le
      (sub_add_cancel 1 t)
  change (MetaMathlibExt.stdGaussianPDFReal x) ^ (1 - t) *
    (MetaMathlibExt.stdGaussianPDFReal y) ^ t ≤
      MetaMathlibExt.stdGaussianPDFReal ((1 - t) • x + t • y)
  unfold MetaMathlibExt.stdGaussianPDFReal
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, Real.mul_rpow hc.le (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_mul, mul_mul_mul_comm, ← Real.rpow_add hc, sub_add_cancel,
    Real.rpow_one, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le
  linarith only [hsq]

private lemma integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa using h

private lemma memLp_sq_gaussianReal : MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  simp_rw [← pow_mul]
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (by simp [integrableExpSet_id_gaussianReal]) 4

private lemma variance_sq_gaussianReal : Var[fun x : ℝ ↦ x ^ 2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub memLp_sq_gaussianReal]
  change (∫ x, (x ^ 2) ^ 2 ∂gaussianReal 0 1) - (∫ x, x ^ 2 ∂gaussianReal 0 1) ^ 2 = 2
  simp_rw [← pow_mul]
  norm_num [ProbabilityTheory.integral_pow_four_gaussianReal, integral_sq_gaussianReal]

private lemma measurePreserving_stdGaussian_eval {n : ℕ} (i : Fin n) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin n) ↦ x i)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (gaussianReal 0 1) := by
  simpa using measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin n))) (S := (1 : Matrix (Fin n) (Fin n) ℝ))
    (i := i) Matrix.PosSemidef.one

private lemma integral_stdGaussian_eval {n : ℕ} (i : Fin n) :
    ∫ x, (x : EuclideanSpace ℝ (Fin n)) i ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = 0 := by
  rw [← integral_id_gaussianReal (μ := 0) (v := 1),
    ← (measurePreserving_stdGaussian_eval i).map_eq, integral_map]
  all_goals fun_prop

private lemma stdGaussian_coordinate_memLp {n : ℕ} (i : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) 2 (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
  (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving (measurePreserving_stdGaussian_eval i)

private lemma stdGaussian_integral_coordinate_mul {n : ℕ} (i j : Fin n) :
    (∫ x, (x : EuclideanSpace ℝ (Fin n)) i * x j ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      if i = j then 1 else 0 := by
  have h := covariance_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin n))) (S := (1 : Matrix (Fin n) (Fin n) ℝ))
    Matrix.PosSemidef.one i j
  rw [multivariateGaussian_zero_one, covariance_eq_sub (stdGaussian_coordinate_memLp i)
    (stdGaussian_coordinate_memLp j), integral_stdGaussian_eval, integral_stdGaussian_eval,
    mul_zero, sub_zero, Matrix.one_apply] at h
  exact h

private lemma memLp_norm_sq_stdGaussian (n : ℕ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ 2) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact memLp_finsetSum _ fun i _ ↦
    memLp_sq_gaussianReal.comp_measurePreserving (measurePreserving_stdGaussian_eval i)

private lemma integral_norm_sq_stdGaussian (n : ℕ) :
    ∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = n := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · calc
      _ = ∑ _i : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun i _ ↦ by
        rw [← integral_sq_gaussianReal, ← (measurePreserving_stdGaussian_eval i).map_eq,
          integral_map]
        all_goals fun_prop
      _ = n := by simp
  · exact fun i _ ↦ (stdGaussian_coordinate_memLp i).integrable_sq

private lemma variance_norm_sq_stdGaussian (n : ℕ) :
    Var[fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ 2; stdGaussian (EuclideanSpace ℝ (Fin n))] =
      2 * (n : ℝ) := by
  rw [← map_pi_eq_stdGaussian, variance_map (by fun_prop) (by fun_prop)]
  have h : (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ 2) ∘ toLp 2 =
      ∑ i : Fin n, fun x : Fin n → ℝ ↦ x i ^ 2 := by
    ext x
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [h, variance_sum_pi (X := fun _i x ↦ x ^ 2) (fun _ ↦ memLp_sq_gaussianReal)]
  simp [variance_sq_gaussianReal, mul_comm]

private lemma evariance_norm_sq_stdGaussian (n : ℕ) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 2 * (n : ℝ≥0∞) := by
  rw [← integral_norm_sq_stdGaussian n, ← evariance_eq_lintegral_ofReal,
    ← ofReal_variance (memLp_norm_sq_stdGaussian n), variance_norm_sq_stdGaussian,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
  norm_num

/-- **The standard Gaussian has normalized radius variance 2.** For every dimension $n \ge 1$,
the standard Gaussian measure $\gamma_n$ on $\mathbb{R}^n$ is isotropic log-concave (a probability
measure with a log-concave Lebesgue density, mean $0$ and identity covariance), and its normalized
radius variance $\frac{1}{n} \int (|x|^2 - n)^2 \, d\gamma_n(x)$ equals $2$.

Source: Klartag--Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem stdGaussian_isotropic_variance (n : ℕ) (hn : 0 < n) :
    IsIsotropicLogConcave (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      normalizedRadiusVariance
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) = 2 := by
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨MetaMathlibExt.stdGaussianPDFReal, isLogConcaveDensity_stdGaussianPDFReal n,
      MetaMathlibExt.stdGaussian_eq_withDensity⟩
  · intro i
    exact ⟨(stdGaussian_coordinate_memLp i).integrable (by norm_num), integral_stdGaussian_eval i⟩
  · intro i j
    exact ⟨(stdGaussian_coordinate_memLp i).integrable_mul (stdGaussian_coordinate_memLp j),
      stdGaussian_integral_coordinate_mul i j⟩
  · rw [normalizedRadiusVariance, evariance_norm_sq_stdGaussian]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast hn.ne') (by simp)

end

/-- **The thin-shell variance constant is at least 2.** The thin-shell variance constant, the
supremum in $[0, \infty]$ of the normalized radius variances
$\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$ over all dimensions $n \ge 1$ and all isotropic
log-concave probability measures $\mu$ on $\mathbb{R}^n$, is at least $2$.

The lower bound comes from the standard Gaussian, whose normalized radius variance is $2$ in
every dimension.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem two_le_thinShellVarianceConstant :
    2 ≤ thinShellVarianceConstant := by
  obtain ⟨hIso, hVar⟩ := stdGaussian_isotropic_variance 1 Nat.one_pos
  simpa only [hVar] using normalizedRadiusVariance_le_constant Nat.one_pos hIso

end MathlibExt.Probability.ThinShell
