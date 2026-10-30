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
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Dirichlet space `𝒟(𝔻)` and its reproducing kernel

The Dirichlet space `𝒟(𝔻)` is the Hilbert space of holomorphic functions
`f(z) = ∑ₙ aₙ zⁿ` on the open unit disc whose norm
`‖f‖² = ∑ₙ (n + 1) * ‖aₙ‖²` is finite. We model the space by the
coefficients of a function in the orthonormal basis of rescaled monomials
`eₙ(z) = zⁿ / √(n + 1)`, i.e. by `ℓ²(ℕ, ℂ)`: a sequence `b` represents
`f(z) = ∑' n, b n * zⁿ / √(n + 1)`.

Under this identification, point evaluation at `z` in the disc is the
bounded linear functional given by the inner product with the **Dirichlet
kernel** `k_z`, whose coefficients are `(conj z)ⁿ / √(n + 1)`:

* `dirichletKernel z hz : ℓ²(ℕ, ℂ)` has `(k_z)ₙ = (conj z)ⁿ / √(n + 1)`;
* `dirichletEval z hz a = ⟪k_z, a⟫ = ∑' n, a n * zⁿ / √(n + 1)` is point
  evaluation;
* `‖k_z‖² = -log (1 - ‖z‖²) / ‖z‖²` for `z ≠ 0` (and `‖k_0‖² = 1`), so
  evaluation has norm `‖ev_z‖ = √(-log (1 - ‖z‖²) / ‖z‖²)`;
* `⟪k_z, k_w⟫ = -log (1 - z * conj w) / (z * conj w)` is the Dirichlet
  kernel function (with value `1` at `z * conj w = 0`).

This makes `𝒟(𝔻)` a reproducing-kernel Hilbert space. It is a companion
to the Hilbert-space / Fourier material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(the spectral theorem, Bessel's inequality, and the Fejér / Fourier
theory), none of which defines the Dirichlet space or its kernel. It is
not one of the 72 v1 targets, and it is not in the pinned Mathlib
(Mathlib has reproducing-kernel Hilbert spaces in the abstract, but no
Dirichlet space and no Dirichlet kernel) or in base MathlibExt. See e.g.
Agler and McCarthy, *Pick Interpolation and Hilbert Function Spaces*,
Graduate Studies in Mathematics 44, AMS, 2002, or El-Fallah, Kellay,
Mashreghi, and Ransford, *A Primer on the Dirichlet Space*,
Cambridge University Press, 2014, for the classical theory.

## Main declarations

* `dirichletKernel z hz` : the Dirichlet kernel at `z` as an `ℓ²(ℕ, ℂ)` sequence.
* `norm_sq_dirichletKernel_of_ne_zero` : `‖k_z‖² = -log (1 - ‖z‖²) / ‖z‖²`.
* `norm_dirichletKernel_of_ne_zero` : `‖k_z‖ = √(-log (1 - ‖z‖²) / ‖z‖²)`.
* `norm_sq_dirichletKernel_le_inv` : `‖k_z‖² ≤ 1 / (1 - ‖z‖²)`, the
  comparison with the Hardy-space kernel norm.
* `dirichletEval z hz a` : point evaluation, `∑' n, a n * zⁿ / √(n + 1)`.
* `dirichletEvalCLM z hz` : point evaluation as a bounded operator
  `ℓ²(ℕ, ℂ) →L[ℂ] ℂ`.
* `norm_dirichletEvalCLM` : `‖ev_z‖ = ‖k_z‖`.
* `norm_dirichletEval_le` : `‖f(z)‖ ≤ ‖f‖ * ‖k_z‖`.
* `inner_dirichletKernel_dirichletKernel` :
  `⟪k_z, k_w⟫ = ∑' n, (z * conj w)ⁿ / (n + 1)`.
* `inner_dirichletKernel_dirichletKernel_eq_log` :
  `⟪k_z, k_w⟫ = -log (1 - z * conj w) / (z * conj w)` for `z * conj w ≠ 0`.
* `dirichletEval_dirichletKernel_of_ne_zero` : `f_z(k_z) = -log (1 - ‖z‖²) / ‖z‖²`,
  so the pointwise bound is sharp.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.DirichletSpace

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace

/-- The power series `∑' n, rⁿ / (n + 1)` sums to `-log (1 - r) / r`
for `0 < r < 1`: factor `1 / r` out of the logarithm series. -/
theorem hasSum_div_succ_pow_real {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    HasSum (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) (-Real.log (1 - r) / r) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (by rwa [abs_of_pos h0] : |r| < 1)).mul_left (1 / r)
  rw [div_eq_mul_one_div, mul_comm]
  apply h.congr_fun
  intro n
  have hr : r ≠ 0 := ne_of_gt h0
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- The complex form: `∑' n, uⁿ / (n + 1)` sums to `-log (1 - u) / u`
for `u ≠ 0` in the unit disc. -/
theorem hasSum_div_succ_pow_complex {u : ℂ} (h0 : u ≠ 0) (h1 : ‖u‖ < 1) :
    HasSum (fun n : ℕ => u ^ n / ((n : ℂ) + 1)) (-Complex.log (1 - u) / u) := by
  have h := (Complex.hasSum_taylorSeries_neg_log' h1).mul_left (1 / u)
  rw [div_eq_mul_one_div, mul_comm]
  apply h.congr_fun
  intro n
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast h2
  rw [pow_succ]
  field_simp

/-- The squared norms of the Dirichlet kernel coefficients are
`‖z‖ ^ (2 * n) / (n + 1)`. -/
theorem norm_sq_dirichlet_coeff (z : ℂ) (n : ℕ) :
    ‖(starRingEnd ℂ z) ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ)‖ ^ (2 : ℝ) =
      (‖z‖ ^ 2) ^ n / ((n : ℝ) + 1) := by
  rw [Real.rpow_two, norm_div, div_pow, norm_pow, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), ← pow_mul, mul_comm n 2, pow_mul]

/-- The Dirichlet kernel coefficients are summable in the `ℓ²` sense:
`∑' n, (‖z‖²)ⁿ / (n + 1)` converges, by comparison with the geometric series. -/
theorem summable_dirichletKernel_terms (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => (‖z‖ ^ 2) ^ n / ((n : ℝ) + 1)) := by
  have h1 : ‖z‖ ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa using h
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => div_le_self (pow_nonneg (sq_nonneg _) _) (by
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith))
  exact (hasSum_geometric_of_lt_one (sq_nonneg _) h1).summable

/-- The Dirichlet kernel coefficients are in `ℓ²` when `z` is in the disc. -/
theorem memℓp_dirichletKernel (z : ℂ) (hz : ‖z‖ < 1) :
    Memℓp (fun n : ℕ => (starRingEnd ℂ z) ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ)) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, norm_sq_dirichlet_coeff]
  exact summable_dirichletKernel_terms z hz

/-- The **Dirichlet kernel** at `z`: the `ℓ²(ℕ, ℂ)` sequence with
coefficients `(conj z)ⁿ / √(n + 1)`. -/
noncomputable def dirichletKernel (z : ℂ) (hz : ‖z‖ < 1) : ℓ²(ℕ, ℂ) :=
  ⟨fun n => (starRingEnd ℂ z) ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ),
    memℓp_dirichletKernel z hz⟩

@[simp] theorem dirichletKernel_apply (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    dirichletKernel z hz n =
      (starRingEnd ℂ z) ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ) :=
  rfl

/-- The Dirichlet kernel at `0` is the first standard basis vector. -/
theorem dirichletKernel_zero (hz : ‖(0 : ℂ)‖ < 1) :
    dirichletKernel 0 hz = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [dirichletKernel_apply, lp.single_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Pi.single_eq_of_ne hn, map_zero]
    simp [zero_pow hn]

/-- The squared norm of the Dirichlet kernel is `-log (1 - ‖z‖²) / ‖z‖²`. -/
theorem norm_sq_dirichletKernel_of_ne_zero (z : ℂ) (hz : ‖z‖ < 1) (h0 : z ≠ 0) :
    ‖dirichletKernel z hz‖ ^ 2 = -Real.log (1 - ‖z‖ ^ 2) / ‖z‖ ^ 2 := by
  have hr : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
  have h1 : ‖z‖ ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa using h
  have hpow : ‖dirichletKernel z hz‖ ^ (2 : ℝ≥0∞).toReal =
      -Real.log (1 - ‖z‖ ^ 2) / ‖z‖ ^ 2 := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    simp only [h2, dirichletKernel_apply, norm_sq_dirichlet_coeff]
    rw [(hasSum_div_succ_pow_real hr h1).tsum_eq]
  have h2' : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [h2', Real.rpow_two] at hpow
  exact hpow

/-- The squared norm of the Dirichlet kernel at `0` is `1`. -/
theorem norm_sq_dirichletKernel_zero (hz : ‖(0 : ℂ)‖ < 1) :
    ‖dirichletKernel 0 hz‖ ^ 2 = 1 := by
  rw [dirichletKernel_zero, lp.norm_single (by simp), norm_one]
  norm_num

/-- The norm of the Dirichlet kernel is `√(-log (1 - ‖z‖²) / ‖z‖²)`. -/
theorem norm_dirichletKernel_of_ne_zero (z : ℂ) (hz : ‖z‖ < 1) (h0 : z ≠ 0) :
    ‖dirichletKernel z hz‖ = Real.sqrt (-Real.log (1 - ‖z‖ ^ 2) / ‖z‖ ^ 2) := by
  rw [← norm_sq_dirichletKernel_of_ne_zero z hz h0, Real.sqrt_sq (norm_nonneg _)]

/-- The norm of the Dirichlet kernel at `0` is `1`. -/
theorem norm_dirichletKernel_zero (hz : ‖(0 : ℂ)‖ < 1) :
    ‖dirichletKernel 0 hz‖ = 1 := by
  rw [dirichletKernel_zero, lp.norm_single (by simp), norm_one]

/-- The Dirichlet kernel norm is bounded by the Hardy kernel norm:
`‖k_z‖² ≤ 1 / (1 - ‖z‖²)`, via `log x ≤ x - 1` at `x = (1 - ‖z‖²)⁻¹`. -/
theorem norm_sq_dirichletKernel_le_inv (z : ℂ) (hz : ‖z‖ < 1) :
    ‖dirichletKernel z hz‖ ^ 2 ≤ 1 / (1 - ‖z‖ ^ 2) := by
  by_cases h0 : z = 0
  · subst h0
    rw [norm_sq_dirichletKernel_zero]
    simp
  · rw [norm_sq_dirichletKernel_of_ne_zero z hz h0]
    have hr : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
    have h1 : ‖z‖ ^ 2 < 1 := by
      have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
      simpa using h
    have hne : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr h1)
    have hlog : -Real.log (1 - ‖z‖ ^ 2) ≤ ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < (1 - ‖z‖ ^ 2)⁻¹ from inv_pos.mpr (sub_pos.mpr h1))
      rw [Real.log_inv] at h
      have hthis : (1 - ‖z‖ ^ 2)⁻¹ - 1 = ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by
        field_simp
        ring
      linarith
    have h2 : (1 : ℝ) / (1 - ‖z‖ ^ 2) * ‖z‖ ^ 2 = ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by ring
    rw [div_le_iff₀ hr, h2]
    exact hlog

/-- Point evaluation on `𝒟(𝔻)`: the inner product with the Dirichlet kernel. -/
noncomputable def dirichletEval (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) : ℂ :=
  ⟪dirichletKernel z hz, a⟫

/-- Point evaluation is the Taylor series `∑' n, a n * zⁿ / √(n + 1)`. -/
theorem dirichletEval_eq_tsum (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    dirichletEval z hz a = ∑' n, a n * z ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  unfold dirichletEval
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [dirichletKernel_apply, RCLike.inner_apply', map_div₀, map_pow, RCLike.conj_conj,
    Complex.conj_ofReal]
  ring

/-- The Taylor series of a `𝒟` function converges absolutely at every
point of the disc. -/
theorem summable_dirichletEval_terms (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * z ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ)) := by
  have hs := (lp.hasSum_inner (𝕜 := ℂ) (dirichletKernel z hz) a).summable
  apply hs.congr
  intro n
  rw [dirichletKernel_apply, RCLike.inner_apply', map_div₀, map_pow, RCLike.conj_conj,
    Complex.conj_ofReal]
  ring

/-- Point evaluation as a bounded linear functional on `𝒟(𝔻)`. -/
noncomputable def dirichletEvalCLM (z : ℂ) (hz : ‖z‖ < 1) : ℓ²(ℕ, ℂ) →L[ℂ] ℂ :=
  innerSL ℂ (dirichletKernel z hz)

/-- The bounded point-evaluation functional acts by the inner product
with the Dirichlet kernel. -/
theorem dirichletEvalCLM_apply (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    dirichletEvalCLM z hz a = dirichletEval z hz a :=
  rfl

/-- The operator norm of point evaluation is the norm of the kernel. -/
theorem norm_dirichletEvalCLM (z : ℂ) (hz : ‖z‖ < 1) :
    ‖dirichletEvalCLM z hz‖ = ‖dirichletKernel z hz‖ := by
  show ‖innerSL ℂ (dirichletKernel z hz)‖ = ‖dirichletKernel z hz‖
  rw [innerSL_apply_norm]

/-- The operator norm of point evaluation is `√(-log (1 - ‖z‖²) / ‖z‖²)`. -/
theorem norm_dirichletEvalCLM_of_ne_zero (z : ℂ) (hz : ‖z‖ < 1) (h0 : z ≠ 0) :
    ‖dirichletEvalCLM z hz‖ = Real.sqrt (-Real.log (1 - ‖z‖ ^ 2) / ‖z‖ ^ 2) := by
  rw [norm_dirichletEvalCLM, norm_dirichletKernel_of_ne_zero z hz h0]

/-- The operator norm of point evaluation at `0` is `1`. -/
theorem norm_dirichletEvalCLM_zero (hz : ‖(0 : ℂ)‖ < 1) :
    ‖dirichletEvalCLM 0 hz‖ = 1 := by
  rw [norm_dirichletEvalCLM, norm_dirichletKernel_zero]

/-- The pointwise bound for `𝒟` functions: `‖f(z)‖ ≤ ‖f‖ * ‖k_z‖`. -/
theorem norm_dirichletEval_le (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    ‖dirichletEval z hz a‖ ≤ ‖a‖ * ‖dirichletKernel z hz‖ := by
  calc ‖dirichletEval z hz a‖ = ‖dirichletEvalCLM z hz a‖ := by
        rw [dirichletEvalCLM_apply]
    _ ≤ ‖dirichletEvalCLM z hz‖ * ‖a‖ := (dirichletEvalCLM z hz).le_opNorm a
    _ = ‖a‖ * ‖dirichletKernel z hz‖ := by
        rw [norm_dirichletEvalCLM]
        ring

/-- Evaluation at `0` is the constant Taylor coefficient. -/
theorem dirichletEval_zero (a : ℓ²(ℕ, ℂ)) (hz : ‖(0 : ℂ)‖ < 1) :
    dirichletEval 0 hz a = a 0 := by
  unfold dirichletEval
  rw [dirichletKernel_zero hz, lp.inner_single_left, RCLike.inner_apply']
  simp

/-- Evaluation of a monomial `c * zⁿ / √(n + 1)` (a single coefficient). -/
theorem dirichletEval_single (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) (c : ℂ) :
    dirichletEval z hz (lp.single 2 n c) =
      c * z ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  unfold dirichletEval
  rw [lp.inner_single_right, RCLike.inner_apply', dirichletKernel_apply,
    map_div₀, map_pow, RCLike.conj_conj, Complex.conj_ofReal]
  ring

/-- The reproducing property in the other order: `⟪a, k_z⟫ = conj (f(z))`. -/
theorem inner_dirichletKernel_right (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    ⟪a, dirichletKernel z hz⟫ = (starRingEnd ℂ) (dirichletEval z hz a) := by
  unfold dirichletEval
  rw [← inner_conj_symm]

/-- The inner product of two Dirichlet kernels is the power series
`∑' n, (z * conj w)ⁿ / (n + 1)`. -/
theorem inner_dirichletKernel_dirichletKernel (z : ℂ) (hz : ‖z‖ < 1) (w : ℂ)
    (hw : ‖w‖ < 1) :
    ⟪dirichletKernel z hz, dirichletKernel w hw⟫ =
      ∑' (n : ℕ), (z * (starRingEnd ℂ w)) ^ n / ((n : ℂ) + 1) := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ n : ℕ,
      ⟪dirichletKernel z hz n, dirichletKernel w hw n⟫_ℂ =
        (z * (starRingEnd ℂ w)) ^ n / ((n : ℂ) + 1) := by
    intro n
    rw [dirichletKernel_apply, dirichletKernel_apply, RCLike.inner_apply', map_div₀, map_pow,
      RCLike.conj_conj, Complex.conj_ofReal, mul_pow]
    have hsq : ((Real.sqrt ((n : ℝ) + 1) : ℂ)) ^ 2 = ((n : ℂ) + 1) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      push_cast
      ring
    rw [div_mul_div_comm, ← sq, hsq]
  simp only [hterm]

/-- The inner product of two Dirichlet kernels is the Dirichlet kernel
function `-log (1 - z * conj w) / (z * conj w)`. -/
theorem inner_dirichletKernel_dirichletKernel_eq_log (z : ℂ) (hz : ‖z‖ < 1) (w : ℂ)
    (hw : ‖w‖ < 1) (h0 : z * (starRingEnd ℂ w) ≠ 0) :
    ⟪dirichletKernel z hz, dirichletKernel w hw⟫ =
      -Complex.log (1 - z * (starRingEnd ℂ w)) / (z * (starRingEnd ℂ w)) := by
  rw [inner_dirichletKernel_dirichletKernel z hz w hw]
  have hnorm : ‖z * (starRingEnd ℂ w)‖ < 1 := by
    rw [norm_mul, RCLike.norm_conj]
    calc ‖z‖ * ‖w‖ < 1 * 1 :=
          mul_lt_mul'' hz hw (norm_nonneg z) (norm_nonneg w)
      _ = 1 := one_mul 1
  exact (hasSum_div_succ_pow_complex h0 hnorm).tsum_eq

/-- Evaluation of the kernel at its own point: `f_z(k_z) = ‖k_z‖²`. -/
theorem dirichletEval_dirichletKernel (z : ℂ) (hz : ‖z‖ < 1) :
    dirichletEval z hz (dirichletKernel z hz) =
      ((‖dirichletKernel z hz‖ ^ 2 : ℝ) : ℂ) := by
  unfold dirichletEval
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- Evaluation of the kernel at its own point, in closed form:
`f_z(k_z) = -log (1 - ‖z‖²) / ‖z‖²`, so the pointwise bound is sharp. -/
theorem dirichletEval_dirichletKernel_of_ne_zero (z : ℂ) (hz : ‖z‖ < 1) (h0 : z ≠ 0) :
    dirichletEval z hz (dirichletKernel z hz) =
      ((-Real.log (1 - ‖z‖ ^ 2) / ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [dirichletEval_dirichletKernel, norm_sq_dirichletKernel_of_ne_zero z hz h0]

end MathlibExt.Analysis.InnerProductSpace.DirichletSpace
