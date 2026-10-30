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
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Fock (Segal–Bargmann) space and its reproducing kernel

The Fock space is the Hilbert space of entire functions on `ℂ` whose
Taylor coefficients are square-summable against the factorial weights:
a function `f(z) = ∑ₙ aₙ zⁿ / √(n!)` belongs to the space exactly when
`∑ₙ ‖aₙ‖² < ∞`. We model it by its Taylor-coefficient sequence in
`ℓ²(ℕ, ℂ)`, i.e. by the orthonormal basis `eₙ(z) = zⁿ / √(n!)`.
Under this identification, point evaluation at `z ∈ ℂ` is the bounded
linear functional given by the inner product with the **Fock kernel**
`k_z`, whose coefficients are `(conj z)ⁿ / √(n!)`:

* `fockKernel z : ℓ²(ℕ, ℂ)` has `(k_z)ₙ = (conj z)ⁿ / √(n!)`;
* `fockEval z a = ⟪k_z, a⟫ = ∑' n, a n * zⁿ / √(n!)` is point evaluation;
* `‖k_z‖² = Real.exp ‖z‖²`, so evaluation has norm
  `‖ev_z‖ = Real.exp (‖z‖² / 2)`;
* `⟪k_z, k_w⟫ = Complex.exp (z * conj w)` is the Fock kernel function.

Unlike the Hardy space `H²(𝔻)` and the Bergman space `A²(𝔻)`, which live
on the unit disc, the Fock space lives on all of `ℂ`: no `‖z‖ < 1`
hypothesis is needed anywhere. The normalized kernels
`ĉ_z = Real.exp (-‖z‖² / 2) • k_z` are the coherent states of the quantum
harmonic oscillator; their overlap is Gaussian,
`‖⟪ĉ_z, ĉ_w⟫‖ = Real.exp (-‖z - w‖² / 2)`.

This makes the Fock space a reproducing-kernel Hilbert space: every point
evaluation is bounded and is reproduced by the kernel. It is a companion
to the Hilbert-space / Fourier material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(the spectral theorem, Bessel's inequality, and the Fejér / Fourier
theory), none of which defines the Fock space or its kernel. It is not
one of the 72 v1 targets, and it is not in the pinned Mathlib (Mathlib
has reproducing-kernel Hilbert spaces in the abstract, but no Fock
space and no Bargmann kernel) or in base MathlibExt. See e.g. Conway,
*A Course in Functional Analysis*, Chapter VII, or Folland,
*Harmonic Analysis in Phase Space*, Chapter 1, for the classical theory.

## Main declarations

* `fockKernel z` : the Fock kernel at `z` as an `ℓ²(ℕ, ℂ)` sequence.
* `norm_sq_fockKernel` : `‖k_z‖² = Real.exp ‖z‖²`.
* `norm_fockKernel` : `‖k_z‖ = Real.exp (‖z‖² / 2)`.
* `fockEval z a` : point evaluation, `∑' n, a n * zⁿ / √(n!)`.
* `fockEvalCLM z` : point evaluation as a bounded operator
  `ℓ²(ℕ, ℂ) →L[ℂ] ℂ`.
* `norm_fockEvalCLM` : `‖ev_z‖ = Real.exp (‖z‖² / 2)`.
* `norm_fockEval_le` : `‖f(z)‖ ≤ ‖f‖ * Real.exp (‖z‖² / 2)`.
* `inner_fockKernel_fockKernel` :
  `⟪k_z, k_w⟫ = Complex.exp (z * conj w)`.
* `fockCoherent z` : the normalized kernel (coherent state).
* `norm_inner_fockCoherent_fockCoherent` :
  `‖⟪ĉ_z, ĉ_w⟫‖ = Real.exp (-‖z - w‖² / 2)` (Gaussian overlap).
* `fockMonomial` : the named normalized monomial family.
* `orthonormal_fockMonomial` : the standard orthonormal-family property.
* `fockCoeff_eq_inner` : coefficient extraction using the named monomials.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.FockSpace

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open scoped ComplexInnerProductSpace

/-- The squared norms of the Fock kernel coefficients are
`‖z‖ ^ (2 * n) / n!`. -/
theorem norm_sq_fock_coeff (z : ℂ) (n : ℕ) :
    ‖(starRingEnd ℂ z) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)‖ ^ (2 : ℝ) =
      (‖z‖ ^ 2) ^ n / (Nat.factorial n : ℝ) := by
  rw [Real.rpow_two, norm_div, norm_pow, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm n 2, pow_mul]

/-- The Fock kernel coefficients are in `ℓ²` for every `z : ℂ`, since
`∑' n, ‖z‖ ^ (2 * n) / n! = Real.exp ‖z‖²`. -/
theorem memℓp_fockKernel (z : ℂ) :
    Memℓp (fun n : ℕ => (starRingEnd ℂ z) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, norm_sq_fock_coeff]
  exact (NormedSpace.expSeries_div_hasSum_exp (‖z‖ ^ 2 : ℝ)).summable

/-- The **Fock kernel** at `z`: the `ℓ²(ℕ, ℂ)` sequence with coefficients
`(conj z)ⁿ / √(n!)`. -/
noncomputable def fockKernel (z : ℂ) : ℓ²(ℕ, ℂ) :=
  ⟨fun n => (starRingEnd ℂ z) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ), memℓp_fockKernel z⟩

@[simp] theorem fockKernel_apply (z : ℂ) (n : ℕ) :
    fockKernel z n = (starRingEnd ℂ z) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) :=
  rfl

/-- The Fock kernel at `0` is the first standard basis vector. -/
theorem fockKernel_zero :
    fockKernel (0 : ℂ) = lp.single 2 0 (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [fockKernel_apply, lp.single_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Pi.single_eq_of_ne hn, map_zero, zero_pow hn]
    exact zero_div _

/-- The squared norm of the Fock kernel is `Real.exp ‖z‖²`. -/
theorem norm_sq_fockKernel (z : ℂ) :
    ‖fockKernel z‖ ^ 2 = Real.exp (‖z‖ ^ 2) := by
  have hpow : ‖fockKernel z‖ ^ (2 : ℝ≥0∞).toReal = Real.exp (‖z‖ ^ 2) := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    simp only [h2, fockKernel_apply, norm_sq_fock_coeff]
    have hsum := NormedSpace.expSeries_div_hasSum_exp (‖z‖ ^ 2 : ℝ)
    rw [hsum.tsum_eq, ← Real.exp_eq_exp_ℝ]
  have h2' : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [h2', Real.rpow_two] at hpow
  exact hpow

/-- The norm of the Fock kernel is `Real.exp (‖z‖² / 2)`. -/
theorem norm_fockKernel (z : ℂ) :
    ‖fockKernel z‖ = Real.exp (‖z‖ ^ 2 / 2) := by
  have hsq := norm_sq_fockKernel z
  have hnorm : ‖fockKernel z‖ = Real.sqrt (Real.exp (‖z‖ ^ 2)) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, ← Real.exp_half]

/-- Point evaluation on the Fock space: the inner product with the
Fock kernel. -/
noncomputable def fockEval (z : ℂ) (a : ℓ²(ℕ, ℂ)) : ℂ :=
  ⟪fockKernel z, a⟫

/-- Point evaluation is the Taylor series `∑' n, a n * zⁿ / √(n!)`. -/
theorem fockEval_eq_tsum (z : ℂ) (a : ℓ²(ℕ, ℂ)) :
    fockEval z a = ∑' n, a n * z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) := by
  unfold fockEval
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [fockKernel_apply, RCLike.inner_apply', map_div₀, map_pow, RCLike.conj_conj,
    Complex.conj_ofReal]
  ring

/-- The Taylor series of a Fock-space function converges absolutely at
every point of `ℂ`. -/
theorem summable_fockEval_terms (z : ℂ) (a : ℓ²(ℕ, ℂ)) :
    Summable (fun n => a n * z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) := by
  have hs := (lp.hasSum_inner (𝕜 := ℂ) (fockKernel z) a).summable
  apply hs.congr
  intro n
  rw [fockKernel_apply, RCLike.inner_apply', map_div₀, map_pow, RCLike.conj_conj,
    Complex.conj_ofReal]
  ring

/-- Point evaluation as a bounded linear functional on the Fock space. -/
noncomputable def fockEvalCLM (z : ℂ) : ℓ²(ℕ, ℂ) →L[ℂ] ℂ :=
  innerSL ℂ (fockKernel z)

/-- The bounded point-evaluation functional acts by the inner product
with the Fock kernel. -/
theorem fockEvalCLM_apply (z : ℂ) (a : ℓ²(ℕ, ℂ)) :
    fockEvalCLM z a = fockEval z a :=
  rfl

/-- The operator norm of point evaluation is `Real.exp (‖z‖² / 2)`. -/
theorem norm_fockEvalCLM (z : ℂ) :
    ‖fockEvalCLM z‖ = Real.exp (‖z‖ ^ 2 / 2) := by
  change ‖innerSL ℂ (fockKernel z)‖ = Real.exp (‖z‖ ^ 2 / 2)
  rw [innerSL_apply_norm, norm_fockKernel]

/-- The pointwise bound for Fock-space functions:
`‖f(z)‖ ≤ ‖f‖ * Real.exp (‖z‖² / 2)`. -/
theorem norm_fockEval_le (z : ℂ) (a : ℓ²(ℕ, ℂ)) :
    ‖fockEval z a‖ ≤ ‖a‖ * Real.exp (‖z‖ ^ 2 / 2) := by
  calc ‖fockEval z a‖ = ‖fockEvalCLM z a‖ := by rw [fockEvalCLM_apply]
    _ ≤ ‖fockEvalCLM z‖ * ‖a‖ := (fockEvalCLM z).le_opNorm a
    _ = ‖a‖ * Real.exp (‖z‖ ^ 2 / 2) := by rw [norm_fockEvalCLM, mul_comm]

/-- Evaluation at `0` is the constant Taylor coefficient. -/
theorem fockEval_zero (a : ℓ²(ℕ, ℂ)) :
    fockEval (0 : ℂ) a = a 0 := by
  unfold fockEval
  rw [fockKernel_zero, lp.inner_single_left, RCLike.inner_apply']
  simp

/-- Evaluation of a monomial `c * zⁿ / √(n!)` (a single Taylor
coefficient). -/
theorem fockEval_single (z : ℂ) (n : ℕ) (c : ℂ) :
    fockEval z (lp.single 2 n c) = c * z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) := by
  unfold fockEval
  rw [lp.inner_single_right, RCLike.inner_apply', fockKernel_apply,
    map_div₀, map_pow, RCLike.conj_conj, Complex.conj_ofReal]
  ring

/-- The reproducing property in the other order: `⟪a, k_z⟫ = conj (f(z))`. -/
theorem inner_fockKernel_right (z : ℂ) (a : ℓ²(ℕ, ℂ)) :
    ⟪a, fockKernel z⟫ = (starRingEnd ℂ) (fockEval z a) := by
  unfold fockEval
  rw [← inner_conj_symm]

/-- The inner product of two Fock kernels is the Fock kernel function
`Complex.exp (z * conj w)`. -/
theorem inner_fockKernel_fockKernel (z w : ℂ) :
    ⟪fockKernel z, fockKernel w⟫ = Complex.exp (z * (starRingEnd ℂ w)) := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ n : ℕ,
      ⟪fockKernel z n, fockKernel w n⟫_ℂ =
        (z * (starRingEnd ℂ w)) ^ n / (Nat.factorial n : ℂ) := by
    intro n
    rw [fockKernel_apply, fockKernel_apply, RCLike.inner_apply', map_div₀, map_pow,
      RCLike.conj_conj, Complex.conj_ofReal, div_mul_div_comm, ← mul_pow]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    norm_cast
  simp only [hterm]
  have hsum := NormedSpace.expSeries_div_hasSum_exp (z * (starRingEnd ℂ w))
  rw [hsum.tsum_eq, ← Complex.exp_eq_exp_ℂ]

/-- The norm of the inner product of two Fock kernels is
`Real.exp (z * conj w).re`. -/
theorem norm_inner_fockKernel_fockKernel (z w : ℂ) :
    ‖⟪fockKernel z, fockKernel w⟫‖ = Real.exp (z * (starRingEnd ℂ w)).re := by
  rw [inner_fockKernel_fockKernel, Complex.norm_exp]

/-- Evaluation of the kernel at its own point: `f_z(k_z) = Real.exp ‖z‖²`,
so the pointwise bound is sharp. -/
theorem fockEval_fockKernel (z : ℂ) :
    fockEval z (fockKernel z) = ((Real.exp (‖z‖ ^ 2) : ℝ) : ℂ) := by
  unfold fockEval
  rw [inner_fockKernel_fockKernel, Complex.ofReal_exp, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- The normalized monomial `eₙ(z) = zⁿ / √(n!)`, represented by the `n`th
standard basis vector in the Taylor-coefficient model of Fock space. -/
@[reducible] noncomputable def fockMonomial (n : ℕ) : ℓ²(ℕ, ℂ) :=
  lp.single 2 n (1 : ℂ)

/-- The rescaled monomials `eₙ(z) = zⁿ / √(n!)`, i.e. the standard basis
vectors of the coefficient model, are orthonormal. -/
theorem fockMonomial_orthonormal (m n : ℕ) :
    ⟪fockMonomial m, fockMonomial n⟫_ℂ =
      if m = n then (1 : ℂ) else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : m = n
  · subst h
    simp [Pi.single_eq_same]
  · simp [h]

/-- The normalized monomial family satisfies Mathlib's standard orthonormal predicate. -/
theorem orthonormal_fockMonomial : Orthonormal ℂ fockMonomial :=
  orthonormal_iff_ite.mpr fockMonomial_orthonormal

/-- The coefficient of `a` at `n` is the inner product with `eₙ`. -/
theorem fockCoeff_eq_inner (a : ℓ²(ℕ, ℂ)) (n : ℕ) :
    a n = ⟪fockMonomial n, a⟫ := by
  rw [lp.inner_single_left, RCLike.inner_apply']
  simp

/-- The **coherent state** at `z`: the normalized Fock kernel,
`ĉ_z = Real.exp (-‖z‖² / 2) • k_z`. -/
noncomputable def fockCoherent (z : ℂ) : ℓ²(ℕ, ℂ) :=
  ((Real.exp (-‖z‖ ^ 2 / 2) : ℝ) : ℂ) • fockKernel z

/-- Coherent states are unit vectors. -/
theorem norm_fockCoherent (z : ℂ) : ‖fockCoherent z‖ = 1 := by
  unfold fockCoherent
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_fockKernel, ← Real.exp_add,
    show (-‖z‖ ^ 2 / 2 + ‖z‖ ^ 2 / 2 : ℝ) = 0 by ring, Real.exp_zero]

/-- The inner product of two coherent states. -/
theorem inner_fockCoherent_fockCoherent (z w : ℂ) :
    ⟪fockCoherent z, fockCoherent w⟫ =
      Complex.exp (z * (starRingEnd ℂ w) -
        (((‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 : ℝ) : ℂ)) := by
  unfold fockCoherent
  rw [inner_smul_left, inner_smul_right, inner_fockKernel_fockKernel,
    Complex.conj_ofReal]
  simp only [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The overlap of two coherent states is Gaussian:
`‖⟪ĉ_z, ĉ_w⟫‖ = Real.exp (-‖z - w‖² / 2)`. -/
theorem norm_inner_fockCoherent_fockCoherent (z w : ℂ) :
    ‖⟪fockCoherent z, fockCoherent w⟫‖ = Real.exp (-‖z - w‖ ^ 2 / 2) := by
  have key : (z * (starRingEnd ℂ w)).re =
      (‖z‖ ^ 2 + ‖w‖ ^ 2 - ‖z - w‖ ^ 2) / 2 := by
    have h := Complex.normSq_sub z w
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq] at h
    linarith
  rw [inner_fockCoherent_fockCoherent, Complex.norm_exp]
  have hre : (z * (starRingEnd ℂ w) - (((‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 : ℝ) : ℂ)).re =
      (z * (starRingEnd ℂ w)).re - (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    rw [Complex.sub_re, Complex.ofReal_re]
  rw [hre, key]
  ring_nf

end MathlibExt.Analysis.InnerProductSpace.FockSpace
