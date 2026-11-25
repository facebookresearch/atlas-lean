/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.GreensOperator
public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.ODE.GreensOperatorTrace

open MathlibExt.Analysis.ODE.GreensOperator
open MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

/-!
# Green coefficients, the diagonal kernel integral, and the squared Hilbert–Schmidt norm

The canonical Green eigenvalues for the Dirichlet Laplacian on `[0, 1]` have
sum `1 / 6` and squared sum `1 / 90`. The canonical kernel has diagonal
integral `1 / 6`. These scalar identities follow from Mathlib's Basel values.

For a continuous operator with the canonical self-adjoint and Green kernel
hypotheses, `hsNormSq_greensOperator` identifies its squared Hilbert–Schmidt
norm on the proved sine Hilbert basis with `ENNReal.ofReal (1 / 90)`. The
proof uses the actual operator eigendecomposition and a convergent series.
Existence of that continuous operator, operator trace and trace-classness
are outside this development.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory` (GreensSqrt section): `greensKernel`, `greensEigenvalue`,
and `greens_operator_eigendecomposition` (Theorem, May 13, 2021 section).
The canonical port and its proved sine Hilbert basis are imported unchanged.
-/

/-- The rescaled Basel series over `ℕ`: `∑' n, 1 / (n²π²) = 1 / 6`. -/
private theorem hasSum_greensEigenvalues_nat :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) (1 / 6) := by
  have hpi2 : (Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have h := hasSum_zeta_two.div_const (Real.pi ^ 2)
  have hfun : (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 / Real.pi ^ 2) =
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) := by
    funext n
    rw [div_div]
  rw [hfun] at h
  have hpi : Real.pi ^ 2 / 6 / Real.pi ^ 2 = 1 / 6 := by field_simp
  rwa [hpi] at h

/-- **The Green's eigenvalues are summable.** The Green's eigenvalues
$\lambda_k = 1/(k^2\pi^2)$, indexed by the positive integers $k$, form a summable family of real
numbers. -/
theorem summable_greensEigenvalues : Summable greensEigenvalue := by
  change Summable (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2))
  have h := (hasSum_pnat_iff
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) (a := 1 / 6)).mpr
    (by simpa using hasSum_greensEigenvalues_nat)
  exact h.summable

/-- **The Green's eigenvalues tend to zero.** The Green's eigenvalues
$\lambda_k = 1/(k^2\pi^2)$ tend to $0$ along the cofinite filter on the positive integers, that
is, $\lambda_k \to 0$ as $k \to \infty$. -/
theorem tendsto_cofinite_greensEigenvalues :
    Filter.Tendsto greensEigenvalue Filter.cofinite (nhds 0) :=
  summable_greensEigenvalues.tendsto_cofinite_zero

/-- **Sum of the Green's eigenvalues.** For the Green's eigenvalues $\lambda_k = 1/(k^2\pi^2)$,
indexed by the positive integers $k$, we have $\sum_{k \ge 1} \lambda_k = 1/6$. -/
theorem tsum_greensEigenvalues : (∑' k : ℕ+, greensEigenvalue k) = 1 / 6 := by
  have h := (hasSum_pnat_iff
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) (a := 1 / 6)).mpr
    (by simpa using hasSum_greensEigenvalues_nat)
  simpa only [greensEigenvalue] using h.tsum_eq

/-- The rescaled `ζ(4)` series over `ℕ`: `∑' n, 1 / (n⁴π⁴) = 1 / 90`. -/
private theorem hasSum_greensEigenvalues_sq_nat :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 4 * Real.pi ^ 4)) (1 / 90) := by
  have hpi4 : (Real.pi : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 Real.pi_ne_zero
  have h := hasSum_zeta_four.div_const (Real.pi ^ 4)
  have hfun : (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4 / Real.pi ^ 4) =
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 4 * Real.pi ^ 4)) := by
    funext n
    rw [div_div]
  rw [hfun] at h
  have hpi : Real.pi ^ 4 / 90 / Real.pi ^ 4 = 1 / 90 := by field_simp
  rwa [hpi] at h

/-- The squared canonical Green eigenvalues form a convergent series. -/
private theorem hasSum_greensEigenvalues_sq :
    HasSum (fun k : ℕ+ => (greensEigenvalue k) ^ 2) (1 / 90) := by
  have h := (hasSum_pnat_iff
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 4 * Real.pi ^ 4)) (a := 1 / 90)).mpr
    (by simpa using hasSum_greensEigenvalues_sq_nat)
  have hsq : (fun k : ℕ+ => (1 : ℝ) / (((k : ℕ) : ℝ) ^ 4 * Real.pi ^ 4)) =
      (fun k : ℕ+ => ((1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2) := by
    funext k
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.pos.ne'
    have hpi2 : (Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
    field_simp
  rw [hsq] at h
  simpa only [greensEigenvalue] using h

/-- **Sum of the squared Green's eigenvalues.** For the Green's eigenvalues
$\lambda_k = 1/(k^2\pi^2)$, indexed by the positive integers $k$, we have
$\sum_{k \ge 1} \lambda_k^2 = 1/90$. -/
theorem tsum_greensEigenvalues_sq :
    (∑' k : ℕ+, (greensEigenvalue k) ^ 2) = 1 / 90 :=
  hasSum_greensEigenvalues_sq.tsum_eq

/-- **Diagonal integral of the Green's kernel.** The Green's kernel $G$ on $[0, 1]$ satisfies
$\int_0^1 G(x, x)\,dx = 1/6$, since $G(x, x) = x(1 - x)$. -/
theorem integral_greensKernel_diag :
    ∫ x in (0 : ℝ)..1, greensKernel x x = 1 / 6 := by
  change (∫ x in (0 : ℝ)..1, min x x * (1 - max x x)) = 1 / 6
  have h : ∀ x : ℝ, min x x * (1 - max x x) = x - x ^ 2 := by
    intro x
    rw [min_self, max_self]
    ring
  simp_rw [h]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => t ^ 2 / 2 - t ^ 3 / 3) (x - x ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      convert (hasDerivAt_pow 2 x).div_const 2 using 1
      field_simp
      ring
    have h2 : HasDerivAt (fun t : ℝ => t ^ 3 / 3) (x ^ 2) x := by
      convert (hasDerivAt_pow 3 x).div_const 3 using 1
      field_simp
      ring
    convert h1.sub h2 using 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_id.sub (continuous_pow 2)).intervalIntegrable 0 1)]
  norm_num

/-- **The Green's eigenvalues sum to the diagonal integral of the kernel.** The sum of the
Green's eigenvalues $\lambda_k = 1/(k^2\pi^2)$ over the positive integers $k$ equals the integral
of the Green's kernel $G$ along the diagonal: $\sum_{k \ge 1} \lambda_k = \int_0^1 G(x, x)\,dx$. -/
theorem greens_eigenvalue_sum_eq_kernel_diagonal_integral :
    (∑' k : ℕ+, greensEigenvalue k) =
      ∫ x in (0 : ℝ)..1, greensKernel x x := by
  rw [tsum_greensEigenvalues, integral_greensKernel_diag]

/-- **Squared Hilbert–Schmidt norm of the Green's operator.** Let
$G(x, t) = \min(x, t)\,(1 - \max(x, t))$ be the Green's kernel and let $A$ be a continuous linear
operator on $L^2([0, 1])$ that is symmetric, $\langle Af, g \rangle = \langle f, Ag \rangle$ for
all $f, g$, and is given by the Green's kernel, $(Af)(x) = \int_{[0, 1]} G(x, t) f(t)\, dt$ for
almost every $x \in [0, 1]$ and every $f$. Let $(b_k)_{k \ge 1}$ be the sine Hilbert basis of
$L^2([0, 1])$. Then the squared Hilbert–Schmidt norm of $A$ in the family $(b_{n+1})_{n \ge 0}$
equals $1/90$, that is, $\sum_{n \ge 0} \|A b_{n+1}\|^2 = 1/90$, the sum being taken in
$[0, \infty]$. -/
theorem hsNormSq_greensOperator
    (A : L2UnitInterval →L[ℝ] L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t)) :
    hsNormSq A (fun n : ℕ => sineHilbertBasis ⟨n + 1, Nat.succ_pos n⟩) =
      ENNReal.ofReal (1 / 90 : ℝ) := by
  have hdec := greens_operator_eigendecomposition A.toLinearMap sineHilbertBasis
    hA_sa sineHilbertBasis_coe hA_greens
  have heig (k : ℕ+) :
      A (sineHilbertBasis k) = greensEigenvalue k • sineHilbertBasis k :=
    Module.End.mem_eigenspace_iff.mp
      ((Module.End.hasEigenvector_iff.mp (hdec.2.1 k)).1)
  have hnorm (k : ℕ+) : ‖A (sineHilbertBasis k)‖ ^ 2 = (greensEigenvalue k) ^ 2 := by
    rw [heig k, norm_smul, sineHilbertBasis.orthonormal.norm_eq_one k,
      mul_one, Real.norm_eq_abs, sq_abs]
  let k : ℕ → ℕ+ := fun n => ⟨n + 1, Nat.succ_pos n⟩
  let f : ℕ → ℝ := fun n => (greensEigenvalue (k n)) ^ 2
  have hf : HasSum f (1 / 90) := by
    change HasSum (fun n : ℕ => ((1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2) (1 / 90)
    have h := (hasSum_pnat_iff_hasSum_succ
      (f := fun n : ℕ => ((1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2)).mp
      (by simpa only [greensEigenvalue] using hasSum_greensEigenvalues_sq)
    exact h
  change (∑' n : ℕ, ENNReal.ofReal
    (‖A (sineHilbertBasis (k n))‖ ^ 2)) = ENNReal.ofReal (1 / 90 : ℝ)
  calc
    (∑' n : ℕ, ENNReal.ofReal (‖A (sineHilbertBasis (k n))‖ ^ 2)) =
        ∑' n : ℕ, ENNReal.ofReal (f n) := by
      apply tsum_congr
      intro n
      exact congrArg ENNReal.ofReal (hnorm (k n))
    _ = ENNReal.ofReal (1 / 90 : ℝ) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hf.summable, hf.tsum_eq]

end MathlibExt.Analysis.ODE.GreensOperatorTrace
