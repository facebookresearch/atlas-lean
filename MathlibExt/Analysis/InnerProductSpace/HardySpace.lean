/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hardy space `H²(𝔻)` and its Szegő kernel

The Hardy space `H²(𝔻)` is the Hilbert space of holomorphic functions
`f(z) = ∑ₙ aₙ zⁿ` on the open unit disc whose Taylor coefficients are
square-summable: `∑ₙ ‖aₙ‖² < ∞`. We model it by its Taylor-coefficient
sequence in `ℓ²(ℕ, ℂ)`, which is the standard identification (via the
Fourier basis on the circle, the coefficients with `n ≥ 0` are exactly
the analytic part of an `L²` function on the circle). Under this
identification, point evaluation at `z` in the disc is the bounded
linear functional given by the inner product with the **Szegő kernel**
`k_z`, whose coefficients are `(conj z)ⁿ`:

* `szegoKernel z hz : ℓ²(ℕ, ℂ)` has `(k_z)ₙ = (conj z)ⁿ`;
* `hardyEval z hz a = ⟪k_z, a⟫ = ∑' n, a n * zⁿ` is point evaluation;
* `‖k_z‖² = 1 / (1 - ‖z‖²)`, so evaluation has norm
  `‖ev_z‖ = 1 / √(1 - ‖z‖²)`;
* `⟪k_z, k_w⟫ = 1 / (1 - z * conj w)` is the Szegő kernel function.

This makes `H²(𝔻)` a reproducing-kernel Hilbert space: every point
evaluation is bounded and is reproduced by the kernel. It is a
companion to the Hilbert-space / Fourier material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(the spectral theorem, Bessel's inequality, and the Fejér / Fourier
theory), none of which defines the Hardy space or its kernel. It is
not one of the 72 v1 targets, and it is not in the pinned Mathlib
(Mathlib has reproducing-kernel Hilbert spaces in the abstract, but
no Hardy space and no Szegő kernel) or in base MathlibExt. See e.g.
Conway, *A Course in Functional Analysis*, Chapter VII, or
Duren, *Theory of `H^p` Spaces*, for the classical theory.

## Main declarations

* `szegoKernel z hz` : the Szegő kernel at `z` as an `ℓ²(ℕ, ℂ)` sequence.
* `norm_sq_szegoKernel` : `‖k_z‖² = 1 / (1 - ‖z‖²)`.
* `norm_szegoKernel` : `‖k_z‖ = 1 / √(1 - ‖z‖²)`.
* `hardyEval z hz a` : point evaluation, `∑' n, a n * zⁿ`.
* `hardyEvalCLM z hz` : point evaluation as a bounded operator
  `ℓ²(ℕ, ℂ) →L[ℂ] ℂ`.
* `norm_hardyEvalCLM` : `‖ev_z‖ = 1 / √(1 - ‖z‖²)`.
* `norm_hardyEval_le` : `‖f(z)‖ ≤ ‖f‖ / √(1 - ‖z‖²)`.
* `inner_szegoKernel_szegoKernel` :
  `⟪k_z, k_w⟫ = 1 / (1 - z * conj w)`.
* `abs_coeff_le_norm` : `‖a n‖ ≤ ‖a‖` for Taylor coefficients.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.HardySpace

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace

/-- The squared norms of the Szegő kernel coefficients form a geometric
progression with ratio `‖z‖²`. -/
theorem norm_sq_szego_coeff (z : ℂ) (n : ℕ) :
    ‖(starRingEnd ℂ z) ^ n‖ ^ (2 : ℝ) = (‖z‖ ^ 2) ^ n := by
  rw [Real.rpow_two, norm_pow, RCLike.norm_conj, ← pow_mul, mul_comm n 2, pow_mul]

/-- The Szegő kernel coefficients are in `ℓ²` when `z` is in the disc. -/
theorem memℓp_szegoKernel (z : ℂ) (hz : ‖z‖ < 1) :
    Memℓp (fun n => (starRingEnd ℂ z) ^ n) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, norm_sq_szego_coeff]
  have h1 : ‖z‖ ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa using h
  exact summable_geometric_of_lt_one (by positivity) h1

/-- The **Szegő kernel** at `z`: the `ℓ²(ℕ, ℂ)` sequence with
coefficients `(conj z)ⁿ`. -/
noncomputable def szegoKernel (z : ℂ) (hz : ‖z‖ < 1) : ℓ²(ℕ, ℂ) :=
  ⟨fun n => (starRingEnd ℂ z) ^ n, memℓp_szegoKernel z hz⟩

@[simp] theorem szegoKernel_apply (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    szegoKernel z hz n = (starRingEnd ℂ z) ^ n :=
  rfl

/-- The Szegő kernel at `0` is the first standard basis vector. -/
theorem szegoKernel_zero (hz : ‖(0 : ℂ)‖ < 1) :
    szegoKernel 0 hz = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [szegoKernel_apply, lp.single_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Pi.single_eq_of_ne hn, map_zero]
    exact zero_pow hn

/-- The squared norm of the Szegő kernel is `1 / (1 - ‖z‖²)`. -/
theorem norm_sq_szegoKernel (z : ℂ) (hz : ‖z‖ < 1) :
    ‖szegoKernel z hz‖ ^ 2 = 1 / (1 - ‖z‖ ^ 2) := by
  have h1 : ‖z‖ ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa using h
  have hpow : ‖szegoKernel z hz‖ ^ (2 : ℝ≥0∞).toReal = 1 / (1 - ‖z‖ ^ 2) := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    simp only [h2, szegoKernel_apply, norm_sq_szego_coeff]
    rw [tsum_geometric_of_lt_one (by positivity) h1]
    rw [one_div]
  have h2' : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [h2', Real.rpow_two] at hpow
  exact hpow

/-- The norm of the Szegő kernel is `1 / √(1 - ‖z‖²)`. -/
theorem norm_szegoKernel (z : ℂ) (hz : ‖z‖ < 1) :
    ‖szegoKernel z hz‖ = 1 / Real.sqrt (1 - ‖z‖ ^ 2) := by
  have hsq := norm_sq_szegoKernel z hz
  have hnorm : ‖szegoKernel z hz‖ = Real.sqrt (1 / (1 - ‖z‖ ^ 2)) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

/-- Point evaluation on `H²(𝔻)`: the inner product with the Szegő kernel. -/
noncomputable def hardyEval (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) : ℂ :=
  ⟪szegoKernel z hz, a⟫

/-- Point evaluation is the Taylor series `∑' n, a n * zⁿ`. -/
theorem hardyEval_eq_tsum (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    hardyEval z hz a = ∑' n, a n * z ^ n := by
  unfold hardyEval
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [szegoKernel_apply, RCLike.inner_apply', map_pow, RCLike.conj_conj,
    mul_comm (z ^ n) (a n)]

/-- The Taylor series of an `H²` function converges absolutely at every
point of the disc. -/
theorem summable_hardyEval_terms (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * z ^ n) := by
  have hs := (lp.hasSum_inner (𝕜 := ℂ) (szegoKernel z hz) a).summable
  apply hs.congr
  intro n
  rw [szegoKernel_apply, RCLike.inner_apply', map_pow, RCLike.conj_conj,
    mul_comm (z ^ n) (a n)]

/-- Point evaluation as a bounded linear functional on `H²(𝔻)`. -/
noncomputable def hardyEvalCLM (z : ℂ) (hz : ‖z‖ < 1) : ℓ²(ℕ, ℂ) →L[ℂ] ℂ :=
  innerSL ℂ (szegoKernel z hz)

/-- The bounded point-evaluation functional acts by the inner product
with the Szegő kernel. -/
theorem hardyEvalCLM_apply (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    hardyEvalCLM z hz a = hardyEval z hz a :=
  rfl

/-- The operator norm of point evaluation is `1 / √(1 - ‖z‖²)`. -/
theorem norm_hardyEvalCLM (z : ℂ) (hz : ‖z‖ < 1) :
    ‖hardyEvalCLM z hz‖ = 1 / Real.sqrt (1 - ‖z‖ ^ 2) := by
  show ‖innerSL ℂ (szegoKernel z hz)‖ = 1 / Real.sqrt (1 - ‖z‖ ^ 2)
  rw [innerSL_apply_norm, norm_szegoKernel]

/-- The pointwise bound for `H²` functions: `‖f(z)‖ ≤ ‖f‖ / √(1 - ‖z‖²)`. -/
theorem norm_hardyEval_le (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    ‖hardyEval z hz a‖ ≤ ‖a‖ / Real.sqrt (1 - ‖z‖ ^ 2) := by
  calc ‖hardyEval z hz a‖ = ‖hardyEvalCLM z hz a‖ := by
        rw [hardyEvalCLM_apply]
    _ ≤ ‖hardyEvalCLM z hz‖ * ‖a‖ := (hardyEvalCLM z hz).le_opNorm a
    _ = ‖a‖ / Real.sqrt (1 - ‖z‖ ^ 2) := by
        rw [norm_hardyEvalCLM]
        ring

/-- Evaluation at `0` is the constant Taylor coefficient. -/
theorem hardyEval_zero (a : ℓ²(ℕ, ℂ)) (hz : ‖(0 : ℂ)‖ < 1) :
    hardyEval 0 hz a = a 0 := by
  unfold hardyEval
  rw [szegoKernel_zero hz, lp.inner_single_left, RCLike.inner_apply']
  simp

/-- Evaluation of a monomial `c * zⁿ` (a single Taylor coefficient). -/
theorem hardyEval_single (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) (c : ℂ) :
    hardyEval z hz (lp.single 2 n c) = c * z ^ n := by
  unfold hardyEval
  rw [lp.inner_single_right, RCLike.inner_apply', szegoKernel_apply,
    map_pow, RCLike.conj_conj, mul_comm (z ^ n) c]

/-- The reproducing property in the other order: `⟪a, k_z⟫ = conj (f(z))`. -/
theorem inner_szegoKernel_right (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    ⟪a, szegoKernel z hz⟫ = (starRingEnd ℂ) (hardyEval z hz a) := by
  unfold hardyEval
  rw [← inner_conj_symm]

/-- The inner product of two Szegő kernels is the Szegő kernel function
`1 / (1 - z * conj w)`. -/
theorem inner_szegoKernel_szegoKernel (z : ℂ) (hz : ‖z‖ < 1) (w : ℂ)
    (hw : ‖w‖ < 1) :
    ⟪szegoKernel z hz, szegoKernel w hw⟫ = (1 - z * (starRingEnd ℂ w))⁻¹ := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ n : ℕ,
      ⟪szegoKernel z hz n, szegoKernel w hw n⟫ = (z * starRingEnd ℂ w) ^ n := by
    intro n
    rw [szegoKernel_apply, szegoKernel_apply, RCLike.inner_apply',
      map_pow, RCLike.conj_conj, ← mul_pow]
  simp only [hterm]
  rw [tsum_geometric_of_norm_lt_one]
  rw [norm_mul, RCLike.norm_conj]
  calc ‖z‖ * ‖w‖ < 1 * 1 :=
        mul_lt_mul'' hz hw (norm_nonneg z) (norm_nonneg w)
    _ = 1 := one_mul 1

/-- Taylor coefficients of an `H²` function are bounded by its norm: a
single squared coefficient is at most the sum of all of them. -/
theorem abs_coeff_le_norm (a : ℓ²(ℕ, ℂ)) (n : ℕ) : ‖a n‖ ≤ ‖a‖ := by
  have hs : Summable (fun i => ‖a i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp a).summable (by simp)
  have hle : ‖a n‖ ^ (2 : ℝ≥0∞).toReal ≤ ∑' i, ‖a i‖ ^ (2 : ℝ≥0∞).toReal := by
    have h := Summable.sum_le_tsum (s := {n})
      (f := fun i => ‖a i‖ ^ (2 : ℝ≥0∞).toReal) (fun i _ => by positivity) hs
    rwa [Finset.sum_singleton] at h
  rw [← lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)] at hle
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [h2, Real.rpow_two, Real.rpow_two] at hle
  exact le_of_sq_le_sq hle (norm_nonneg _)

end MathlibExt.Analysis.InnerProductSpace.HardySpace
