/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

namespace MathlibExt.Analysis.ODE.GreensOperatorTrace

/-!
# The trace of the Green's operator for the Dirichlet Laplacian on `[0, 1]`

The v1 book's Green's operator for `-d²/dx²` with Dirichlet boundary
conditions on `[0, 1]` has kernel `G(x, t) = min(x, t) * (1 - max(x, t))`
and eigenvalues `λ_k = 1 / (k²π²)`, `k = 1, 2, …`, on the sine eigenbasis.
For a compact self-adjoint operator the trace is the sum of its
eigenvalues, and the Hilbert–Schmidt norm squared is the sum of the
squared eigenvalues. This file proves those eigenvalue-series identities
for the Green's operator:

* `∑' k, λ_k = 1 / 6`, i.e. the Green's operator is trace-class with
  trace `1 / 6`;
* `∑' k, λ_k² = 1 / 90`, i.e. its Hilbert–Schmidt norm squared is `1 / 90`;
* the trace formula `∑' k, λ_k = ∫₀¹ G(x, x) dx`, since on the diagonal
  `G(x, x) = x * (1 - x)` integrates to `1 / 6`.

The eigenvalue sums are Mathlib's Basel values
(`hasSum_zeta_two`, `hasSum_zeta_four`) rescaled by `1 / π²` and `1 / π⁴`,
transferred from `ℕ` to `ℕ+` via `hasSum_pnat_iff`. The eigenvalue
coefficients are stated inline, as in
`MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared`, rather than by
redefining the v1 `greensEigenvalue` / `greensKernel` declarations.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory` (GreensSqrt section): `greensKernel`, `greensEigenvalue`,
and `greens_operator_eigendecomposition` (Theorem, May 13, 2021 section).
The eigendecomposition itself is not re-ported here; only the eigenvalue
series and the kernel-diagonal integral are proved.
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

/-- The Green's eigenvalues are summable over `k = 1, 2, …`. -/
theorem summable_greensEigenvalues :
    Summable (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) := by
  have h := (hasSum_pnat_iff
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) (a := 1 / 6)).mpr
    (by simpa using hasSum_greensEigenvalues_nat)
  exact h.summable

/-- The Green's eigenvalues tend to `0` along the cofinite filter. -/
theorem tendsto_cofinite_greensEigenvalues :
    Filter.Tendsto (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2))
      Filter.cofinite (nhds 0) :=
  summable_greensEigenvalues.tendsto_cofinite_zero

/-- **The trace of the Green's operator:** the eigenvalue series sums to
`1 / 6`, `∑' k, λ_k = 1 / 6` with `λ_k = 1 / (k²π²)`. -/
theorem tsum_greensEigenvalues :
    (∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) = 1 / 6 := by
  have h := (hasSum_pnat_iff
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 * Real.pi ^ 2)) (a := 1 / 6)).mpr
    (by simpa using hasSum_greensEigenvalues_nat)
  exact h.tsum_eq

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

/-- **The Hilbert–Schmidt norm squared of the Green's operator:** the
squared eigenvalue series sums to `1 / 90`, `∑' k, λ_k² = 1 / 90`. -/
theorem tsum_greensEigenvalues_sq :
    (∑' k : ℕ+, ((1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2) = 1 / 90 := by
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
  exact h.tsum_eq

/-- The integral of the Green's kernel along the diagonal:
`∫₀¹ G(x, x) dx = 1 / 6`, since `G(x, x) = x * (1 - x)`. -/
theorem integral_greensKernel_diag :
    ∫ x in (0 : ℝ)..1, min x x * (1 - max x x) = 1 / 6 := by
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

/-- **Trace formula for the Green's operator:** the eigenvalue series
equals the integral of the kernel along the diagonal,
`∑' k, λ_k = ∫₀¹ G(x, x) dx = 1 / 6`. -/
theorem greens_trace_formula :
    (∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) =
      ∫ x in (0 : ℝ)..1, min x x * (1 - max x x) := by
  rw [tsum_greensEigenvalues, integral_greensKernel_diag]

#print axioms summable_greensEigenvalues
#print axioms tendsto_cofinite_greensEigenvalues
#print axioms tsum_greensEigenvalues
#print axioms tsum_greensEigenvalues_sq
#print axioms integral_greensKernel_diag
#print axioms greens_trace_formula

end MathlibExt.Analysis.ODE.GreensOperatorTrace
