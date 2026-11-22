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
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

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

end MathlibExt.Probability.ThinShell
