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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Bergman space `A²(𝔻)` and its reproducing kernel

The Bergman space `A²(𝔻)` is the Hilbert space of holomorphic functions
`f(z) = ∑ₙ aₙ zⁿ` on the open unit disc that are square-integrable with
respect to normalized planar area measure `dA / π`, so the disc has measure `1`.
With this normalization, the monomials `zⁿ` are orthogonal, with
`‖zⁿ‖² = 1 / (n + 1)`, so the rescaled monomials `eₙ(z) = √(n + 1) zⁿ`
form an orthonormal basis. We model the space by the coefficients of a
function in this basis, i.e. by `ℓ²(ℕ, ℂ)`: a sequence `b` represents
`f(z) = ∑' n, b n * √(n + 1) * zⁿ`.

Under this identification, point evaluation at `z` in the disc is the
bounded linear functional given by the inner product with the **Bergman
kernel** `k_z`, whose coefficients are `√(n + 1) * (conj z)ⁿ`:

* `bergmanKernel z hz : ℓ²(ℕ, ℂ)` has `(k_z)ₙ = √(n + 1) * (conj z)ⁿ`;
* `bergmanEval z hz a = ⟪k_z, a⟫ = ∑' n, a n * √(n + 1) * zⁿ` is point
  evaluation;
* `‖k_z‖² = 1 / (1 - ‖z‖²)²`, so evaluation has norm
  `‖ev_z‖ = 1 / (1 - ‖z‖²)`;
* `⟪k_z, k_w⟫ = 1 / (1 - z * conj w)²` is the Bergman kernel function.

This makes `A²(𝔻)` a reproducing-kernel Hilbert space. It is a companion
to the Hilbert-space / Fourier material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(the spectral theorem, Bessel's inequality, and the Fejér / Fourier
theory), none of which defines the Bergman space or its kernel. It is
not one of the 72 v1 targets, and it is not in the pinned Mathlib
(Mathlib has reproducing-kernel Hilbert spaces in the abstract, but no
Bergman space and no Bergman kernel) or in base MathlibExt. See e.g.
Conway, *A Course in Functional Analysis*, Chapter VII, or
Duren, *Theory of `H^p` Spaces*, for the classical theory.

## Main declarations

* `bergmanKernel z hz` : the Bergman kernel at `z` as an `ℓ²(ℕ, ℂ)` sequence.
* `norm_sq_bergmanKernel` : `‖k_z‖² = 1 / (1 - ‖z‖²)²`.
* `norm_bergmanKernel` : `‖k_z‖ = 1 / (1 - ‖z‖²)`.
* `bergmanEval z hz a` : point evaluation, `∑' n, a n * √(n + 1) * zⁿ`.
* `bergmanEvalCLM z hz` : point evaluation as a bounded operator
  `ℓ²(ℕ, ℂ) →L[ℂ] ℂ`.
* `norm_bergmanEvalCLM` : `‖ev_z‖ = 1 / (1 - ‖z‖²)`.
* `norm_bergmanEval_le` : `‖f(z)‖ ≤ ‖f‖ / (1 - ‖z‖²)`.
* `inner_bergmanKernel_bergmanKernel` :
  `⟪k_z, k_w⟫ = (1 - z * conj w)⁻¹ ^ 2`.
* `bergmanEval_bergmanKernel` : `f_z(k_z) = ((1 - ‖z‖² : ℝ) : ℂ)⁻¹ ^ 2`,
  so the pointwise bound is sharp.
* `bergmanMonomial` : the family of rescaled monomials in the coefficient model.
* `orthonormal_bergmanMonomial` : `Orthonormal ℂ bergmanMonomial`.
* `bergmanMonomial_orthonormal` : the coordinate inner-product equality.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.BergmanSpace

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace

/-- The Cauchy product of the geometric series with itself: the series
`∑' n, (n + 1) * qⁿ` sums to `(1 - q)⁻¹ ^ 2`. -/
theorem hasSum_succ_mul_pow_complex {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * q ^ n) ((1 - q)⁻¹ ^ 2) := by
  have hgeo := hasSum_geometric_of_norm_lt_one (K := ℂ) hq
  have hnorm : Summable (fun n : ℕ => ‖q ^ n‖) := hgeo.summable.norm
  have hprod := hasSum_sum_range_mul_of_summable_norm hnorm hnorm
  rw [hgeo.tsum_eq] at hprod
  rw [← pow_two] at hprod
  apply hprod.congr_fun
  intro n
  have hterm : ∀ k ∈ Finset.range (n + 1), q ^ k * q ^ (n - k) = q ^ n := by
    intro k hk
    rw [← pow_add]
    congr 1
    exact Nat.add_sub_cancel' (Finset.mem_range_succ_iff.mp hk)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The real form of the Cauchy product above. -/
theorem hasSum_succ_mul_pow_real {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) ((1 - r)⁻¹ ^ 2) := by
  have hgeo := hasSum_geometric_of_lt_one h0 h1
  have hnorm : Summable (fun n : ℕ => ‖r ^ n‖) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
    exact hgeo.summable
  have hprod := hasSum_sum_range_mul_of_summable_norm hnorm hnorm
  rw [hgeo.tsum_eq] at hprod
  rw [← pow_two] at hprod
  apply hprod.congr_fun
  intro n
  have hterm : ∀ k ∈ Finset.range (n + 1), r ^ k * r ^ (n - k) = r ^ n := by
    intro k hk
    rw [← pow_add]
    congr 1
    exact Nat.add_sub_cancel' (Finset.mem_range_succ_iff.mp hk)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The squared norms of the Bergman kernel coefficients are
`(n + 1) * ‖z‖ ^ (2 * n)`. -/
theorem norm_sq_bergman_coeff (z : ℂ) (n : ℕ) :
    ‖(starRingEnd ℂ z) ^ n * (Real.sqrt ((n : ℝ) + 1) : ℂ)‖ ^ (2 : ℝ) =
      ((n : ℝ) + 1) * (‖z‖ ^ 2) ^ n := by
  rw [Real.rpow_two, norm_mul, norm_pow, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), ← pow_mul, mul_comm n 2, pow_mul]
  ring

/-- The Bergman kernel coefficients are in `ℓ²` when `z` is in the disc. -/
theorem memℓp_bergmanKernel (z : ℂ) (hz : ‖z‖ < 1) :
    Memℓp (fun n : ℕ => (starRingEnd ℂ z) ^ n * (Real.sqrt ((n : ℝ) + 1) : ℂ)) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, norm_sq_bergman_coeff]
  have h1 : ‖z‖ ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa using h
  exact (hasSum_succ_mul_pow_real (sq_nonneg _) h1).summable

/-- The **Bergman kernel** at `z`: the `ℓ²(ℕ, ℂ)` sequence with
coefficients `√(n + 1) * (conj z)ⁿ`. -/
noncomputable def bergmanKernel (z : ℂ) (hz : ‖z‖ < 1) : ℓ²(ℕ, ℂ) :=
  ⟨fun n => (starRingEnd ℂ z) ^ n * (Real.sqrt ((n : ℝ) + 1) : ℂ),
    memℓp_bergmanKernel z hz⟩

@[simp] theorem bergmanKernel_apply (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    bergmanKernel z hz n =
      (starRingEnd ℂ z) ^ n * (Real.sqrt ((n : ℝ) + 1) : ℂ) :=
  rfl

/-- The Bergman kernel at `0` is the first standard basis vector. -/
theorem bergmanKernel_zero (hz : ‖(0 : ℂ)‖ < 1) :
    bergmanKernel 0 hz = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [bergmanKernel_apply, lp.single_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Pi.single_eq_of_ne hn, map_zero]
    simp [zero_pow hn]

/-- The squared norm of the Bergman kernel is `1 / (1 - ‖z‖²)²`. -/
theorem norm_sq_bergmanKernel (z : ℂ) (hz : ‖z‖ < 1) :
    ‖bergmanKernel z hz‖ ^ 2 = 1 / (1 - ‖z‖ ^ 2) ^ 2 := by
  have h1 : ‖z‖ ^ 2 < 1 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    simpa using h
  have hpow : ‖bergmanKernel z hz‖ ^ (2 : ℝ≥0∞).toReal = 1 / (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    simp only [h2, bergmanKernel_apply, norm_sq_bergman_coeff]
    rw [(hasSum_succ_mul_pow_real (sq_nonneg _) h1).tsum_eq]
    rw [one_div, ← inv_pow]
  have h2' : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [h2', Real.rpow_two] at hpow
  exact hpow

/-- The norm of the Bergman kernel is `1 / (1 - ‖z‖²)`. -/
theorem norm_bergmanKernel (z : ℂ) (hz : ‖z‖ < 1) :
    ‖bergmanKernel z hz‖ = 1 / (1 - ‖z‖ ^ 2) := by
  have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by
    have h := pow_lt_pow_left₀ hz (norm_nonneg z) (by norm_num : (2 : ℕ) ≠ 0)
    have h' : ‖z‖ ^ 2 < 1 := by simpa using h
    linarith
  have hsq := norm_sq_bergmanKernel z hz
  have hnorm : ‖bergmanKernel z hz‖ = Real.sqrt (1 / (1 - ‖z‖ ^ 2) ^ 2) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, one_div, ← inv_pow, Real.sqrt_sq (le_of_lt (inv_pos.mpr hpos)), one_div]

/-- Point evaluation on `A²(𝔻)`: the inner product with the Bergman kernel. -/
noncomputable def bergmanEval (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) : ℂ :=
  ⟪bergmanKernel z hz, a⟫

/-- Point evaluation is the Taylor series `∑' n, a n * √(n + 1) * zⁿ`. -/
theorem bergmanEval_eq_tsum (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    bergmanEval z hz a = ∑' n, a n * (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n := by
  unfold bergmanEval
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [bergmanKernel_apply, RCLike.inner_apply', map_mul, map_pow, RCLike.conj_conj,
    Complex.conj_ofReal]
  ring

/-- The Taylor series of an `A²` function converges absolutely at every
point of the disc. -/
theorem summable_bergmanEval_terms (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n) := by
  have hs := (lp.hasSum_inner (𝕜 := ℂ) (bergmanKernel z hz) a).summable
  apply hs.congr
  intro n
  rw [bergmanKernel_apply, RCLike.inner_apply', map_mul, map_pow, RCLike.conj_conj,
    Complex.conj_ofReal]
  ring

/-- Point evaluation as a bounded linear functional on `A²(𝔻)`. -/
noncomputable def bergmanEvalCLM (z : ℂ) (hz : ‖z‖ < 1) : ℓ²(ℕ, ℂ) →L[ℂ] ℂ :=
  innerSL ℂ (bergmanKernel z hz)

/-- The bounded point-evaluation functional acts by the inner product
with the Bergman kernel. -/
theorem bergmanEvalCLM_apply (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    bergmanEvalCLM z hz a = bergmanEval z hz a :=
  rfl

/-- The operator norm of point evaluation is `1 / (1 - ‖z‖²)`. -/
theorem norm_bergmanEvalCLM (z : ℂ) (hz : ‖z‖ < 1) :
    ‖bergmanEvalCLM z hz‖ = 1 / (1 - ‖z‖ ^ 2) := by
  show ‖innerSL ℂ (bergmanKernel z hz)‖ = 1 / (1 - ‖z‖ ^ 2)
  rw [innerSL_apply_norm, norm_bergmanKernel]

/-- The pointwise bound for `A²` functions: `‖f(z)‖ ≤ ‖f‖ / (1 - ‖z‖²)`. -/
theorem norm_bergmanEval_le (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    ‖bergmanEval z hz a‖ ≤ ‖a‖ / (1 - ‖z‖ ^ 2) := by
  calc ‖bergmanEval z hz a‖ = ‖bergmanEvalCLM z hz a‖ := by
        rw [bergmanEvalCLM_apply]
    _ ≤ ‖bergmanEvalCLM z hz‖ * ‖a‖ := (bergmanEvalCLM z hz).le_opNorm a
    _ = ‖a‖ / (1 - ‖z‖ ^ 2) := by
        rw [norm_bergmanEvalCLM]
        ring

/-- Evaluation at `0` is the constant Taylor coefficient. -/
theorem bergmanEval_zero (a : ℓ²(ℕ, ℂ)) (hz : ‖(0 : ℂ)‖ < 1) :
    bergmanEval 0 hz a = a 0 := by
  unfold bergmanEval
  rw [bergmanKernel_zero hz, lp.inner_single_left, RCLike.inner_apply']
  simp

/-- Evaluation of a monomial `c * √(n + 1) * zⁿ` (a single coefficient). -/
theorem bergmanEval_single (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) (c : ℂ) :
    bergmanEval z hz (lp.single 2 n c) = c * (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n := by
  unfold bergmanEval
  rw [lp.inner_single_right, RCLike.inner_apply', bergmanKernel_apply,
    map_mul, map_pow, RCLike.conj_conj, Complex.conj_ofReal]
  ring

/-- The reproducing property in the other order: `⟪a, k_z⟫ = conj (f(z))`. -/
theorem inner_bergmanKernel_right (z : ℂ) (hz : ‖z‖ < 1) (a : ℓ²(ℕ, ℂ)) :
    ⟪a, bergmanKernel z hz⟫ = (starRingEnd ℂ) (bergmanEval z hz a) := by
  unfold bergmanEval
  rw [← inner_conj_symm]

/-- The inner product of two Bergman kernels is the Bergman kernel function
`(1 - z * conj w)⁻¹ ^ 2`. -/
theorem inner_bergmanKernel_bergmanKernel (z : ℂ) (hz : ‖z‖ < 1) (w : ℂ)
    (hw : ‖w‖ < 1) :
    ⟪bergmanKernel z hz, bergmanKernel w hw⟫ = (1 - z * (starRingEnd ℂ w))⁻¹ ^ 2 := by
  rw [lp.inner_eq_tsum]
  have hnorm : ‖z * (starRingEnd ℂ w)‖ < 1 := by
    rw [norm_mul, RCLike.norm_conj]
    calc ‖z‖ * ‖w‖ < 1 * 1 :=
          mul_lt_mul'' hz hw (norm_nonneg z) (norm_nonneg w)
      _ = 1 := one_mul 1
  have hterm : ∀ n : ℕ,
      ⟪bergmanKernel z hz n, bergmanKernel w hw n⟫_ℂ =
        ((n : ℂ) + 1) * (z * (starRingEnd ℂ w)) ^ n := by
    intro n
    rw [bergmanKernel_apply, bergmanKernel_apply, RCLike.inner_apply', map_mul, map_pow,
      RCLike.conj_conj, Complex.conj_ofReal, mul_pow]
    have hsq : ((Real.sqrt ((n : ℝ) + 1) : ℂ)) ^ 2 = ((n : ℂ) + 1) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      push_cast
      ring
    calc z ^ n * (Real.sqrt ((n : ℝ) + 1) : ℂ) *
          ((starRingEnd ℂ w) ^ n * (Real.sqrt ((n : ℝ) + 1) : ℂ))
        = ((Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 1) : ℂ)) *
            (z ^ n * (starRingEnd ℂ w) ^ n) := by ring
      _ = ((n : ℂ) + 1) * (z ^ n * (starRingEnd ℂ w) ^ n) := by
          rw [← sq, hsq]
  simp only [hterm]
  exact (hasSum_succ_mul_pow_complex hnorm).tsum_eq

/-- Evaluation of the kernel at its own point: `f_z(k_z) = (1 - ‖z‖²)⁻¹ ^ 2`,
so the pointwise bound is sharp. -/
theorem bergmanEval_bergmanKernel (z : ℂ) (hz : ‖z‖ < 1) :
    bergmanEval z hz (bergmanKernel z hz) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)⁻¹ ^ 2 := by
  unfold bergmanEval
  rw [inner_bergmanKernel_bergmanKernel, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_sub, Complex.ofReal_one]

/-- The rescaled monomial `eₙ(z) = √(n + 1) zⁿ` for normalized area
measure `dA / π`, represented by the `n`th standard basis vector in the
coefficient model. -/
noncomputable def bergmanMonomial (n : ℕ) : ℓ²(ℕ, ℂ) :=
  lp.single 2 n (1 : ℂ)

/-- The coordinate inner products of the rescaled monomials equal the
Kronecker delta. -/
theorem bergmanMonomial_orthonormal (m n : ℕ) :
    ⟪(lp.single 2 m (1 : ℂ) : ℓ²(ℕ, ℂ)), (lp.single 2 n (1 : ℂ) : ℓ²(ℕ, ℂ))⟫_ℂ =
      if m = n then (1 : ℂ) else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : m = n
  · subst h
    simp [Pi.single_eq_same]
  · simp [h]

/-- The rescaled monomial family satisfies Mathlib's standard orthonormal
predicate. -/
theorem orthonormal_bergmanMonomial : Orthonormal ℂ bergmanMonomial :=
  orthonormal_iff_ite.mpr bergmanMonomial_orthonormal

/-- The coefficient of `a` at `n` is the inner product with `eₙ`. -/
theorem bergmanCoeff_eq_inner (a : ℓ²(ℕ, ℂ)) (n : ℕ) :
    a n = ⟪lp.single 2 n (1 : ℂ), a⟫ := by
  rw [lp.inner_single_left, RCLike.inner_apply']
  simp

end MathlibExt.Analysis.InnerProductSpace.BergmanSpace
