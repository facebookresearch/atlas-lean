/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.TuringPatterns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Turing instability with cross-diffusion (Keller–Segel-type systems)

`Domains.Biology.Dynamics.TuringPatterns` treats two-species reaction-diffusion systems with a
*diagonal* diffusion matrix `D = diag(d_u, d_v)`. Many biological systems have *cross-diffusion*:
the flux of one species depends on the gradient of the other. The archetype is Keller–Segel
chemotaxis (Keller and Segel 1970), where cells `u` climb the gradient of a chemical `v` they
secrete,

  `u_t = (d_u u_x - χ u v_x)_x + f(u, v)`,   `v_t = d_v v_xx + g(u, v)`.

Linearizing at a homogeneous steady state `(u₀, v₀)` gives `w_t = D w_xx + J w` with the full
(non-symmetric) diffusion matrix `D = [[d_u, -χ u₀], [0, d_v]]` (`kellerSegelFlux_add`), and in
general with any real `2 × 2` matrix `D`. This file develops the linear Turing theory for an
arbitrary diffusion matrix `D`.

The Fourier mode `e^{μ t} cos(k x) v` solves the linearized system iff `(J - k² D) v = μ v`, and
`det (J - k² D) = h(k²)` with the cross-diffusion dispersion polynomial

  `h(q) = det D · q² - b q + det J`,   `b = J₀₀ D₁₁ + J₁₁ D₀₀ - J₀₁ D₁₀ - J₁₀ D₀₁`,

while `tr (J - k² D) = tr J - k² tr D`. For a diagonal `D` this is `TuringPatterns`'
`dispersionDet` (`crossDispersionDet_diffusionMatrix`). If the kinetics are stable
(`tr J < 0 < det J`), `0 ≤ tr D` and `0 < det D`, some mode is unstable iff
`2 √(det D · det J) < b`. These are algebraic hypotheses only: they allow non-parabolic `D`
such as `[[0, -1], [1, 0]]` (eigenvalues `± i`); normal parabolicity needs `0 < tr D`.

The off-diagonal terms of `D` enter `b` through `-J₀₁ D₁₀ - J₁₀ D₀₁`, and this is what makes
cross-diffusion qualitatively different: with diagonal diffusion `d_u, d_v ≥ 0` a stable
(`tr J < 0 < det J`) self-limiting system (`J₀₀ ≤ 0`, `J₁₁ ≤ 0`) can never be destabilized
(`not_exists_isUnstableMode_of_nonpos`), but chemotactic cross-diffusion can destabilize it. For
Keller–Segel with logistic growth (`r, β, d_u, d_v > 0`),
`f = r u (1 - u)`, `g = α u - β v`, at `(1, α / β)` one has `J = [[-r, 0], [α, -β]]`, so no
diagonal diffusion produces a pattern, while chemotaxis does iff
`2 √(d_u d_v r β) < α χ - r d_v - β d_u` (`kellerSegel_turing_iff`,
`kellerSegel_crossDiffusionDriven`). For the minimal model (`r = 0`, `β > 0`, `d_u, d_v ≥ 0`) at
any density `u₀`, mode `k ≠ 0` is unstable iff `d_u d_v k² < α χ u₀ - β d_u`
(`minimalKellerSegel_isCrossUnstableMode_iff`), the classical chemotactic instability
condition `α χ u₀ > β d_u` in its long-wave limit; on `[0, L]` (`L > 0`) with Neumann conditions
some mode `n ≥ 1` is unstable iff `d_u d_v (π / L)² < α χ u₀ - β d_u`.

Rates, diffusion coefficients and the sensitivity `χ` are dimensionless. Only the *linear*
analysis is formalized: the linearization principle (that linear instability implies nonlinear
instability of the Keller–Segel PDE), pattern selection, and finite-time blow-up of the minimal
model are not covered.

## Main results

* `fourierMode_isCrossLinearizedSolution_iff`, `isCrossUnstableMode_iff_exists_growing`: the
  dispersion relation for a full diffusion matrix.
* `trace_crossModeMatrix`, `det_crossModeMatrix`, `isCrossUnstableMode_iff`: the mode matrix.
* `isCrossUnstableMode_diffusionMatrix_iff`, `crossDispersionDet_diffusionMatrix`: agreement with
  `TuringPatterns` for diagonal diffusion.
* `crossTuring_instability`, `isCrossUnstableMode_iff_crossDispersionDet_neg`,
  `exists_isCrossUnstableMode_iff`: Turing's criterion with cross-diffusion.
* `crossDispersionDet_neg_of_mem_band`, `exists_isCrossUnstableMode_neumannWavenumber`: the
  unstable band and Neumann modes on long intervals.
* `not_exists_isUnstableMode_of_nonpos`: diagonal diffusion cannot destabilize self-limiting
  kinetics.
* `kellerSegel_steadyState`, `jacobianMatrix_kellerSegel`, `kellerSegelFlux_add`: the
  Keller–Segel kinetics, their Jacobian, and the linearization of the chemotactic flux.
* `kellerSegel_turing_iff`, `kellerSegel_crossDiffusionDriven`: chemotaxis-driven instability with
  logistic growth.
* `minimalKellerSegel_steadyState`, `jacobianMatrix_minimalKellerSegel`,
  `minimalKellerSegel_isCrossUnstableMode_iff`, `minimalKellerSegel_not_isCrossUnstableMode_zero`,
  `minimalKellerSegel_exists_neumann_iff`: the minimal Keller–Segel model.

## References

* E. F. Keller and L. A. Segel, *Initiation of slime mold aggregation viewed as an instability*,
  J. Theor. Biol. 26 (1970) 399–415.
* J. D. Murray, *Mathematical Biology II*, 3rd ed., Springer (2003), §5.3 (chemotaxis) and ch. 2.
* V. K. Vanag and I. R. Epstein, *Cross-diffusion and pattern formation in reaction–diffusion
  systems*, Phys. Chem. Chem. Phys. 11 (2009) 897–912.
* T. Hillen and K. J. Painter, *A user's guide to PDE models for chemotaxis*, J. Math. Biol. 58
  (2009) 183–217.
-/

@[expose] public section

open Matrix Filter Topology

namespace MathlibExt.Biology.Dynamics.TuringCrossDiffusion

open MathlibExt.Biology.Dynamics.TuringPatterns

/-! ### Definitions -/

/-- The mode matrix `J - k² D` of the Fourier mode of wavenumber `k` for the linearized system
`w_t = D w_xx + J w` with an arbitrary (possibly non-diagonal) diffusion matrix `D`. -/
def crossModeMatrix (J D : Matrix (Fin 2) (Fin 2) ℝ) (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  J - k ^ 2 • D

/-- The Fourier mode of wavenumber `k` is *linearly unstable* for the cross-diffusion system:
`J - k² D` has a complex eigenvalue with positive real part. -/
def IsCrossUnstableMode (J D : Matrix (Fin 2) (Fin 2) ℝ) (k : ℝ) : Prop :=
  ∃ μ : ℂ, 0 < μ.re ∧ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (crossModeMatrix J D k).map (↑) *ᵥ v = μ • v

/-- `w` is a classical solution of the linearized cross-diffusion system `w_t = D w_xx + J w`
on `ℝ × ℝ`: `w(t, ·)` is twice differentiable with derivatives `wx`, `wxx`, and `w(·, x)` has the
prescribed time derivative. -/
def IsCrossLinearizedSolution (J D : Matrix (Fin 2) (Fin 2) ℝ)
    (w : ℝ → ℝ → Fin 2 → ℂ) : Prop :=
  ∃ wx wxx : ℝ → ℝ → Fin 2 → ℂ, ∀ t x,
    HasDerivAt (w t) (wx t x) x ∧ HasDerivAt (wx t) (wxx t x) x ∧
    HasDerivAt (fun s => w s x) (D.map (↑) *ᵥ wxx t x + J.map (↑) *ᵥ w t x) t

/-- The mixed coefficient `b = J₀₀ D₁₁ + J₁₁ D₀₀ - J₀₁ D₁₀ - J₁₀ D₀₁` of the cross-diffusion
dispersion polynomial. The last two terms are the cross-diffusion contribution. -/
def crossCoeff (J D : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  J 0 0 * D 1 1 + J 1 1 * D 0 0 - J 0 1 * D 1 0 - J 1 0 * D 0 1

/-- The cross-diffusion dispersion polynomial `h(q) = det D · q² - b q + det J`, so that
`det (J - k² D) = h(k²)` (`det_crossModeMatrix`). -/
def crossDispersionDet (J D : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) : ℝ :=
  D.det * q ^ 2 - crossCoeff J D * q + J.det

/-- The discriminant `b² - 4 det D det J` of the cross-diffusion dispersion polynomial. -/
def crossBandDiscriminant (J D : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  crossCoeff J D ^ 2 - 4 * D.det * J.det

/-- Lower end `(b - √Δ) / (2 det D)` of the unstable band of squared wavenumbers (meaningful for
`0 < det D` and `0 < Δ`; `√Δ = 0` for `Δ < 0`, and the quotient is `0` when `det D = 0`). -/
noncomputable def crossBandLower (J D : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (crossCoeff J D - Real.sqrt (crossBandDiscriminant J D)) / (2 * D.det)

/-- Upper end `(b + √Δ) / (2 det D)` of the unstable band of squared wavenumbers (meaningful for
`0 < det D` and `0 < Δ`; `√Δ = 0` for `Δ < 0`, and the quotient is `0` when `det D = 0`). -/
noncomputable def crossBandUpper (J D : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (crossCoeff J D + Real.sqrt (crossBandDiscriminant J D)) / (2 * D.det)

/-! ### The mode matrix and the dispersion relation -/

/-- `tr (J - k² D) = tr J - k² tr D`. -/
theorem trace_crossModeMatrix (J D : Matrix (Fin 2) (Fin 2) ℝ) (k : ℝ) :
    (crossModeMatrix J D k).trace = J.trace - k ^ 2 * D.trace := by
  simp only [crossModeMatrix, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

/-- `det (J - k² D) = h(k²)`. -/
theorem det_crossModeMatrix (J D : Matrix (Fin 2) (Fin 2) ℝ) (k : ℝ) :
    (crossModeMatrix J D k).det = crossDispersionDet J D (k ^ 2) := by
  simp only [crossModeMatrix, crossDispersionDet, crossCoeff, Matrix.det_fin_two,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Mode `k` is unstable iff `0 < tr (J - k² D)` or `det (J - k² D) < 0` (Routh–Hurwitz). -/
theorem isCrossUnstableMode_iff {J D : Matrix (Fin 2) (Fin 2) ℝ} {k : ℝ} :
    IsCrossUnstableMode J D k ↔
      0 < (crossModeMatrix J D k).trace ∨ (crossModeMatrix J D k).det < 0 :=
  exists_eigenvalue_re_pos_iff _

/-- For a diagonal diffusion matrix the mode matrix is `TuringPatterns.modeMatrix`. -/
theorem crossModeMatrix_diffusionMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ) :
    crossModeMatrix J (diffusionMatrix du dv) k = modeMatrix J du dv k :=
  rfl

/-- For a diagonal diffusion matrix, cross-diffusion instability is `TuringPatterns`'
instability. -/
theorem isCrossUnstableMode_diffusionMatrix_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ} :
    IsCrossUnstableMode J (diffusionMatrix du dv) k ↔ IsUnstableMode J du dv k :=
  Iff.rfl

/-- For a diagonal diffusion matrix, `b = d_v f_u + d_u g_v`. -/
theorem crossCoeff_diffusionMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ) :
    crossCoeff J (diffusionMatrix du dv) = dv * J 0 0 + du * J 1 1 := by
  simp [crossCoeff, diffusionMatrix]
  ring

/-- For a diagonal diffusion matrix the cross-diffusion dispersion polynomial is
`TuringPatterns.dispersionDet`. -/
theorem crossDispersionDet_diffusionMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv q : ℝ) :
    crossDispersionDet J (diffusionMatrix du dv) q = dispersionDet J du dv q := by
  rw [crossDispersionDet, crossCoeff_diffusionMatrix, dispersionDet, diffusionMatrix,
    Matrix.det_fin_two]
  simp

/-! The next three derivative lemmas repeat private lemmas of `TuringPatterns.lean`
(`fourierMode_hasDerivAt_space`, `fourierMode_hasDerivAt_space_second`,
`fourierMode_hasDerivAt_time`). -/

/-- The `x`-derivative of the Fourier mode: `-k e^{μ t} sin(k x) v` (copy of a private lemma of
`TuringPatterns.lean`). -/
private theorem fourierMode_hasDerivAt_space' (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ) (t x : ℝ) :
    HasDerivAt (fourierMode μ k v t)
      ((Complex.exp (μ * t) * ((-k * Real.sin (k * x) : ℝ) : ℂ)) • v) x := by
  change HasDerivAt
    (fun y => (Complex.exp (μ * t) * (Real.cos (k * y) : ℂ)) • v) _ x
  have h := (Real.hasDerivAt_cos (k * x)).comp x ((hasDerivAt_id x).const_mul k)
  simpa [fourierMode, mul_comm, mul_left_comm, mul_assoc] using
    (h.ofReal_comp.const_mul (Complex.exp (μ * t))).smul_const v

/-- The second `x`-derivative of the Fourier mode: `-k² e^{μ t} cos(k x) v` (copy of a private
lemma of `TuringPatterns.lean`). -/
private theorem fourierMode_hasDerivAt_space_second' (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ)
    (t x : ℝ) :
    HasDerivAt
      (fun y => (Complex.exp (μ * t) * ((-k * Real.sin (k * y) : ℝ) : ℂ)) • v)
      ((Complex.exp (μ * t) * ((-k ^ 2 * Real.cos (k * x) : ℝ) : ℂ)) • v) x := by
  have h : HasDerivAt (fun y => -k * Real.sin (k * y))
      (-k ^ 2 * Real.cos (k * x)) x := by
    convert ((Real.hasDerivAt_sin (k * x)).comp x
      ((hasDerivAt_id x).const_mul k)).const_mul (-k) using 1 <;>
      simp
    ring
  exact (h.ofReal_comp.const_mul (Complex.exp (μ * t))).smul_const v

/-- The `t`-derivative of the Fourier mode: `μ e^{μ t} cos(k x) v` (copy of a private lemma of
`TuringPatterns.lean`). -/
private theorem fourierMode_hasDerivAt_time' (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ) (t x : ℝ) :
    HasDerivAt (fun s => fourierMode μ k v s x)
      ((μ * Complex.exp (μ * t) * (Real.cos (k * x) : ℂ)) • v) t := by
  simpa [fourierMode, mul_comm, mul_left_comm, mul_assoc] using
    ((((hasDerivAt_id t).ofReal_comp.const_mul μ).cexp).mul_const
      (Real.cos (k * x) : ℂ)).smul_const v

/-- `D (-k² v) + J v = (J - k² D) v` over `ℂ`. -/
private theorem crossModeMatrix_mulVec (J D : Matrix (Fin 2) (Fin 2) ℝ) (k : ℝ)
    (v : Fin 2 → ℂ) :
    D.map (↑) *ᵥ (-(k : ℂ) ^ 2 • v) + J.map (↑) *ᵥ v =
      (crossModeMatrix J D k).map (↑) *ᵥ v := by
  funext i
  simp [crossModeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- **Dispersion relation with cross-diffusion.** The Fourier mode `e^{μ t} cos(k x) v` is a
classical solution of `w_t = D w_xx + J w` iff `(J - k² D) v = μ v`. -/
theorem fourierMode_isCrossLinearizedSolution_iff (J D : Matrix (Fin 2) (Fin 2) ℝ) (k : ℝ)
    (μ : ℂ) (v : Fin 2 → ℂ) :
    IsCrossLinearizedSolution J D (fourierMode μ k v) ↔
      (crossModeMatrix J D k).map (↑) *ᵥ v = μ • v := by
  constructor
  · rintro ⟨wx, wxx, h⟩
    have hwx : wx 0 = fun x =>
        (Complex.exp (μ * 0) * ((-k * Real.sin (k * x) : ℝ) : ℂ)) • v := by
      funext x
      exact (h 0 x).1.unique (fourierMode_hasDerivAt_space' μ k v 0 x)
    have hwxx := (h 0 0).2.1
    rw [hwx] at hwxx
    have hsecond := hwxx.unique (fourierMode_hasDerivAt_space_second' μ k v 0 0)
    have htime := (h 0 0).2.2.unique (fourierMode_hasDerivAt_time' μ k v 0 0)
    simp only [mul_zero, Real.cos_zero, Complex.ofReal_one, mul_one, Complex.ofReal_neg,
      Complex.ofReal_pow] at hsecond htime
    rw [hsecond] at htime
    simpa [fourierMode, ← crossModeMatrix_mulVec J D k v] using htime
  · intro h
    refine ⟨(fun t x =>
      (Complex.exp (μ * t) * ((-k * Real.sin (k * x) : ℝ) : ℂ)) • v),
      (fun t x => (Complex.exp (μ * t) * ((-k ^ 2 * Real.cos (k * x) : ℝ) : ℂ)) • v),
      ?_⟩
    intro t x
    refine ⟨fourierMode_hasDerivAt_space' μ k v t x,
      fourierMode_hasDerivAt_space_second' μ k v t x, ?_⟩
    have hbase := (crossModeMatrix_mulVec J D k v).trans h
    have hpde : D.map (↑) *ᵥ
        ((Complex.exp (μ * t) * ((-k ^ 2 * Real.cos (k * x) : ℝ) : ℂ)) • v) +
        J.map (↑) *ᵥ fourierMode μ k v t x =
        (μ * Complex.exp (μ * t) * (Real.cos (k * x) : ℂ)) • v := by
      funext i
      have hi := congrFun hbase i
      simp only [fourierMode, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.map_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_pow] at hi ⊢
      linear_combination (Complex.exp (μ * t) * (Real.cos (k * x) : ℂ)) * hi
    rw [hpde]
    exact fourierMode_hasDerivAt_time' μ k v t x

/-- **A Fourier mode of the cross-diffusion system grows iff `J - k² D` has an eigenvalue with
positive real part.** -/
theorem isCrossUnstableMode_iff_exists_growing {J D : Matrix (Fin 2) (Fin 2) ℝ} {k : ℝ} :
    IsCrossUnstableMode J D k ↔ ∃ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      IsCrossLinearizedSolution J D (fourierMode μ k v) ∧
      Tendsto (fun t => ‖fourierMode μ k v t 0‖) atTop atTop := by
  constructor
  · rintro ⟨μ, hμ, v, hv, h⟩
    exact ⟨μ, v, hv, (fourierMode_isCrossLinearizedSolution_iff J D k μ v).2 h,
      (tendsto_norm_fourierMode_iff hv μ k).2 hμ⟩
  · rintro ⟨μ, v, hv, hsol, hgrow⟩
    exact ⟨μ, (tendsto_norm_fourierMode_iff hv μ k).1 hgrow, v, hv,
      (fourierMode_isCrossLinearizedSolution_iff J D k μ v).1 hsol⟩

/-! ### Turing's criterion with cross-diffusion -/

/-- The homogeneous mode is stable when the kinetics are (`tr J < 0 < det J`), whatever `D`. -/
theorem not_isCrossUnstableMode_zero {J : Matrix (Fin 2) (Fin 2) ℝ} (htr : J.trace < 0)
    (hdet : 0 < J.det) (D : Matrix (Fin 2) (Fin 2) ℝ) : ¬ IsCrossUnstableMode J D 0 := by
  rw [isCrossUnstableMode_iff, trace_crossModeMatrix, det_crossModeMatrix]
  simp only [crossDispersionDet]
  push Not
  constructor <;> nlinarith

/-- If `tr J < 0` and `0 ≤ tr D`, mode `k` is unstable iff `h(k²) < 0`. -/
theorem isCrossUnstableMode_iff_crossDispersionDet_neg {J D : Matrix (Fin 2) (Fin 2) ℝ}
    (htr : J.trace < 0) (hD : 0 ≤ D.trace) (k : ℝ) :
    IsCrossUnstableMode J D k ↔ crossDispersionDet J D (k ^ 2) < 0 := by
  rw [isCrossUnstableMode_iff, trace_crossModeMatrix, det_crossModeMatrix]
  have h : J.trace - k ^ 2 * D.trace < 0 := by nlinarith [sq_nonneg k]
  exact ⟨fun h' => h'.resolve_left (not_lt.2 h.le), Or.inr⟩

/-- **Cross-diffusion-driven instability.** If the kinetics are stable (`tr J < 0 < det J`) and
`det (J - k² D) < 0`, the homogeneous mode is stable while mode `k` is unstable. -/
theorem crossTuring_instability {J D : Matrix (Fin 2) (Fin 2) ℝ} {k : ℝ} (htr : J.trace < 0)
    (hdet : 0 < J.det) (hk : (crossModeMatrix J D k).det < 0) :
    ¬ IsCrossUnstableMode J D 0 ∧ IsCrossUnstableMode J D k :=
  ⟨not_isCrossUnstableMode_zero htr hdet D, isCrossUnstableMode_iff.2 (Or.inr hk)⟩

/-- A real quadratic `A q² - S q + C` with `0 < A`, `0 < C` is negative at some `q ≥ 0` iff
`0 < S` and `4 A C < S²`. -/
private theorem exists_quadratic_neg_iff {A S C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    (∃ q, 0 ≤ q ∧ A * q ^ 2 - S * q + C < 0) ↔ 0 < S ∧ 4 * A * C < S ^ 2 := by
  constructor
  · rintro ⟨q, hq, hneg⟩
    have hS : 0 < S := by
      by_contra h
      have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hq
      nlinarith [mul_nonneg hA.le (sq_nonneg q)]
    exact ⟨hS, by nlinarith [mul_neg_of_pos_of_neg hA hneg, sq_nonneg (2 * A * q - S)]⟩
  · rintro ⟨hS, hsq⟩
    refine ⟨S / (2 * A), by positivity, ?_⟩
    have hid : A * (S / (2 * A)) ^ 2 - S * (S / (2 * A)) + C =
        (4 * A * C - S ^ 2) / (4 * A) := by
      field_simp
      ring
    rw [hid]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- For `0 < det D` and `0 < det J`, the dispersion polynomial is negative at some `q ≥ 0` iff
`0 < b` and `4 det D det J < b²`. -/
theorem exists_crossDispersionDet_neg_iff {J D : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D.det)
    (hdet : 0 < J.det) :
    (∃ q, 0 ≤ q ∧ crossDispersionDet J D q < 0) ↔
      0 < crossCoeff J D ∧ 4 * D.det * J.det < crossCoeff J D ^ 2 :=
  exists_quadratic_neg_iff hD hdet

/-- The cross-diffusion Turing condition in squared form: `2 √(det D det J) < b` iff `0 < b` and
`4 det D det J < b²` (for all real inputs: when `det D det J < 0` the square root is `0`). -/
theorem two_mul_sqrt_lt_crossCoeff_iff (J D : Matrix (Fin 2) (Fin 2) ℝ) :
    2 * Real.sqrt (D.det * J.det) < crossCoeff J D ↔
      0 < crossCoeff J D ∧ 4 * D.det * J.det < crossCoeff J D ^ 2 := by
  constructor
  · intro h
    have hS : 0 < crossCoeff J D := lt_of_le_of_lt (by positivity) h
    refine ⟨hS, ?_⟩
    have := (Real.sqrt_lt' (x := D.det * J.det)
      (by linarith : 0 < crossCoeff J D / 2)).1 (by linarith)
    nlinarith
  · rintro ⟨hS, h⟩
    have := (Real.sqrt_lt' (x := D.det * J.det) (half_pos hS)).2 (by nlinarith)
    linarith

/-- **Turing's criterion with cross-diffusion.** If the kinetics are stable (`tr J < 0 < det J`),
`0 ≤ tr D` and `0 < det D`, some Fourier mode is unstable iff `2 √(det D · det J) < b`,
`b = J₀₀ D₁₁ + J₁₁ D₀₀ - J₀₁ D₁₀ - J₁₀ D₀₁`. The hypotheses on `D` do not make it parabolic
(`[[0, -1], [1, 0]]` satisfies them); a normally parabolic `D` (`0 < tr D`, `0 < det D`) is a
special case. -/
theorem exists_isCrossUnstableMode_iff {J D : Matrix (Fin 2) (Fin 2) ℝ} (htr : J.trace < 0)
    (hdet : 0 < J.det) (hDtr : 0 ≤ D.trace) (hDdet : 0 < D.det) :
    (∃ k, IsCrossUnstableMode J D k) ↔ 2 * Real.sqrt (D.det * J.det) < crossCoeff J D := by
  rw [two_mul_sqrt_lt_crossCoeff_iff, ← exists_crossDispersionDet_neg_iff hDdet hdet]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k ^ 2, sq_nonneg k,
      (isCrossUnstableMode_iff_crossDispersionDet_neg htr hDtr k).1 hk⟩
  · rintro ⟨q, hq, h⟩
    refine ⟨Real.sqrt q, (isCrossUnstableMode_iff_crossDispersionDet_neg htr hDtr _).2 ?_⟩
    rwa [Real.sq_sqrt hq]

/-- Squared wavenumbers strictly inside the band `(crossBandLower, crossBandUpper)` make the
dispersion polynomial negative (for `0 < det D`; when `Δ < 0` the band is empty). -/
theorem crossDispersionDet_neg_of_mem_band {J D : Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ}
    (hD : 0 < D.det) (hlo : crossBandLower J D < q) (hhi : q < crossBandUpper J D) :
    crossDispersionDet J D q < 0 := by
  have h2A : 0 < 2 * D.det := by positivity
  unfold crossBandLower at hlo
  unfold crossBandUpper at hhi
  rw [div_lt_iff₀ h2A] at hlo
  rw [lt_div_iff₀ h2A] at hhi
  have hid : 4 * D.det * crossDispersionDet J D q =
      (2 * D.det * q - crossCoeff J D) ^ 2 - crossBandDiscriminant J D := by
    unfold crossDispersionDet crossBandDiscriminant
    ring
  rcases lt_or_ge (crossBandDiscriminant J D) 0 with hΔ | hΔ
  · rw [Real.sqrt_eq_zero'.2 hΔ.le] at hlo hhi
    linarith
  · have hs := Real.sq_sqrt hΔ
    have hsq : (2 * D.det * q - crossCoeff J D) ^ 2 < crossBandDiscriminant J D := by
      have ha : 0 < Real.sqrt (crossBandDiscriminant J D) -
          (2 * D.det * q - crossCoeff J D) := by linarith
      have hb : 0 < (2 * D.det * q - crossCoeff J D) +
          Real.sqrt (crossBandDiscriminant J D) := by linarith
      nlinarith [mul_pos ha hb]
    have h4 : 4 * D.det * crossDispersionDet J D q < 0 := by linarith
    exact neg_of_mul_neg_right h4 (by positivity)

/-- **Large domains pattern.** If the kinetics are stable (`tr J < 0 < det J`), `0 ≤ tr D`,
`0 < det D` and `2 √(det D · det J) < b`, then every long enough interval `[0, L]` has an
unstable nonhomogeneous Neumann mode (`n ≥ 1`), while the homogeneous mode is stable
(`not_isCrossUnstableMode_zero`). -/
theorem exists_isCrossUnstableMode_neumannWavenumber {J D : Matrix (Fin 2) (Fin 2) ℝ}
    (htr : J.trace < 0) (hdet : 0 < J.det) (hDtr : 0 ≤ D.trace) (hDdet : 0 < D.det)
    (h : 2 * Real.sqrt (D.det * J.det) < crossCoeff J D) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∃ n : ℕ, 0 < n ∧
      IsCrossUnstableMode J D (neumannWavenumber L n) := by
  obtain ⟨hS, hsq⟩ := (two_mul_sqrt_lt_crossCoeff_iff J D).1 h
  have hΔ : 0 < crossBandDiscriminant J D := by
    unfold crossBandDiscriminant
    linarith
  have hr : 0 < Real.sqrt (crossBandDiscriminant J D) := Real.sqrt_pos.2 hΔ
  have hp : 0 < 2 * D.det := by positivity
  have hlt : crossBandLower J D < crossBandUpper J D := by
    unfold crossBandLower crossBandUpper
    exact div_lt_div_of_pos_right (by linarith) hp
  have hpos : 0 < crossBandUpper J D := by
    unfold crossBandUpper
    exact div_pos (by linarith) hp
  obtain ⟨L₀, hL₀, hL⟩ := exists_neumann_mem_band hlt hpos
  refine ⟨L₀, hL₀, fun L hL₀L => ?_⟩
  obtain ⟨n, h1, h2⟩ := hL L hL₀L
  have hn := (isCrossUnstableMode_iff_crossDispersionDet_neg htr hDtr _).2
    (crossDispersionDet_neg_of_mem_band hDdet h1 h2)
  refine ⟨n, Nat.pos_of_ne_zero fun h0 => ?_, hn⟩
  subst h0
  exact not_isCrossUnstableMode_zero htr hdet D (by simpa [neumannWavenumber] using hn)

/-! ### Diagonal diffusion cannot destabilize self-limiting kinetics -/

/-- **No Turing pattern without cross-diffusion for self-limiting kinetics.** If the kinetics
are stable (`tr J < 0 < det J`) and both species are self-limiting (`J₀₀ ≤ 0`, `J₁₁ ≤ 0`), then
no diagonal diffusion `d_u, d_v ≥ 0` makes any mode unstable. Turing instability with diagonal
diffusion needs an activator. -/
theorem not_exists_isUnstableMode_of_nonpos {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (htr : J.trace < 0) (hdet : 0 < J.det) (h00 : J 0 0 ≤ 0) (h11 : J 1 1 ≤ 0)
    (hdu : 0 ≤ du) (hdv : 0 ≤ dv) : ¬ ∃ k, IsUnstableMode J du dv k := by
  rintro ⟨k, hk⟩
  rw [isUnstableMode_iff_dispersionDet_neg htr hdu hdv, dispersionDet] at hk
  nlinarith [mul_nonneg (mul_nonneg hdu hdv) (sq_nonneg (k ^ 2)),
    mul_nonneg (mul_nonneg hdv (neg_nonneg.2 h00)) (sq_nonneg k),
    mul_nonneg (mul_nonneg hdu (neg_nonneg.2 h11)) (sq_nonneg k)]

/-! ### Keller–Segel chemotaxis -/

/-- Keller–Segel kinetics on `x = (u, v)`: logistic growth `r u (1 - u)` of the cells (carrying
capacity scaled to `1`) and production `α u` and decay `β v` of the chemoattractant. With
`r = 0` this is the minimal Keller–Segel model. -/
def kellerSegelKinetics (r α β : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![r * x 0 * (1 - x 0), α * x 0 - β * x 1]

/-- The homogeneous steady state `(1, α / β)` of the Keller–Segel kinetics (for `β ≠ 0`; with
`α / 0 = 0` it is `(1, 0)` when `β = 0`). -/
noncomputable def kellerSegelSteadyState (α β : ℝ) : Fin 2 → ℝ :=
  ![1, α / β]

/-- The Jacobian `[[-r, 0], [α, -β]]` of the Keller–Segel kinetics at `(1, α / β)`. -/
def kellerSegelJacobian (r α β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-r, 0; α, -β]

/-- The linearized Keller–Segel diffusion matrix `[[d_u, -χ u₀], [0, d_v]]` at cell density
`u₀`: cell motility `d_u`, chemotactic sensitivity `χ`, chemical diffusivity `d_v`. -/
def kellerSegelDiffusion (du dv χ u₀ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![du, -(χ * u₀); 0, dv]

/-- The Keller–Segel flux `(d_u u_x - χ u v_x, d_v v_x)` at state `x = (u, v)` and gradient
`g = (u_x, v_x)`, so that the system is `w_t = (flux)_x + kinetics`. -/
def kellerSegelFlux (du dv χ : ℝ) (x g : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![du * g 0 - χ * x 0 * g 1, dv * g 1]

/-- **Linearization of the chemotactic flux.** At state `s + p` the flux is the linear map
`kellerSegelDiffusion d_u d_v χ (s 0)` applied to the gradient, plus the remainder
`(-χ p₀ v_x, 0)`, which is bilinear in the perturbation `p` and the gradient `g`. So the
linearized system at a homogeneous state `s` has diffusion matrix
`kellerSegelDiffusion d_u d_v χ (s 0)`. -/
theorem kellerSegelFlux_add (du dv χ : ℝ) (s p g : Fin 2 → ℝ) :
    kellerSegelFlux du dv χ (s + p) g =
      kellerSegelDiffusion du dv χ (s 0) *ᵥ g + ![-(χ * p 0 * g 1), 0] := by
  funext i
  fin_cases i
  · simp [kellerSegelFlux, kellerSegelDiffusion, dotProduct, Fin.sum_univ_two]
    ring
  · simp [kellerSegelFlux, kellerSegelDiffusion, dotProduct, Fin.sum_univ_two]

/-- `(1, α / β)` is a steady state of the Keller–Segel kinetics when `β ≠ 0`. -/
theorem kellerSegel_steadyState (r α : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    kellerSegelKinetics r α β (kellerSegelSteadyState α β) = 0 := by
  funext i
  fin_cases i
  · simp [kellerSegelKinetics, kellerSegelSteadyState]
  · simp [kellerSegelKinetics, kellerSegelSteadyState]
    field_simp
    ring

/-- The Jacobian matrix of the Keller–Segel kinetics at `(1, α / β)` is
`kellerSegelJacobian r α β`. This holds for all real inputs; for `β = 0` the state is `(1, 0)`
(`α / 0 = 0`). -/
theorem jacobianMatrix_kellerSegel (r α β : ℝ) :
    MetaMathlibExt.jacobianMatrix (kellerSegelKinetics r α β) (kellerSegelSteadyState α β) =
      kellerSegelJacobian r α β := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add _
  have h2 : HasDerivAt (fun t : ℝ => α / β + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [kellerSegelSteadyState, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      MetaMathlibExt.jacobianMatrix_apply, kellerSegelKinetics, Pi.add_apply, cons_val_zero,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, cons_val_one, cons_val_fin_one,
      ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero,
      add_zero, kellerSegelJacobian, of_apply, cons_val']
  · rw [((h1.const_mul r).fun_mul (h1.const_sub 1)).deriv]
    ring
  · simp
  · rw [(h1.const_mul α).sub_const (β * (α / β)) |>.deriv]
    ring
  · rw [((h2.const_mul β).const_sub α).deriv]
    ring

/-- `b = α χ u₀ - r d_v - β d_u` for the Keller–Segel system. -/
theorem crossCoeff_kellerSegel (r α β du dv χ u₀ : ℝ) :
    crossCoeff (kellerSegelJacobian r α β) (kellerSegelDiffusion du dv χ u₀) =
      α * χ * u₀ - r * dv - β * du := by
  simp [crossCoeff, kellerSegelJacobian, kellerSegelDiffusion]
  ring

theorem trace_kellerSegelJacobian (r α β : ℝ) :
    (kellerSegelJacobian r α β).trace = -r - β := by
  simp [kellerSegelJacobian, Matrix.trace_fin_two]
  ring

theorem det_kellerSegelJacobian (r α β : ℝ) : (kellerSegelJacobian r α β).det = r * β := by
  simp [kellerSegelJacobian, Matrix.det_fin_two_of]

theorem trace_kellerSegelDiffusion (du dv χ u₀ : ℝ) :
    (kellerSegelDiffusion du dv χ u₀).trace = du + dv := by
  simp [kellerSegelDiffusion, Matrix.trace_fin_two]

theorem det_kellerSegelDiffusion (du dv χ u₀ : ℝ) :
    (kellerSegelDiffusion du dv χ u₀).det = du * dv := by
  simp [kellerSegelDiffusion, Matrix.det_fin_two_of]

/-- Without chemotaxis (`χ = 0`) the Keller–Segel diffusion matrix is diagonal. -/
theorem kellerSegelDiffusion_zero (du dv u₀ : ℝ) :
    kellerSegelDiffusion du dv 0 u₀ = diffusionMatrix du dv := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kellerSegelDiffusion, diffusionMatrix]

/-- **Chemotaxis-driven instability with logistic growth.** For `r, β, d_u, d_v > 0`, the
Keller–Segel state `(1, α / β)` (stable for the kinetics) has an unstable Fourier mode iff
`2 √(d_u d_v r β) < α χ - r d_v - β d_u`. -/
theorem kellerSegel_turing_iff {r α β du dv χ : ℝ} (hr : 0 < r) (hβ : 0 < β) (hdu : 0 < du)
    (hdv : 0 < dv) :
    (∃ k, IsCrossUnstableMode (kellerSegelJacobian r α β) (kellerSegelDiffusion du dv χ 1) k) ↔
      2 * Real.sqrt (du * dv * (r * β)) < α * χ - r * dv - β * du := by
  rw [exists_isCrossUnstableMode_iff (by rw [trace_kellerSegelJacobian]; linarith)
      (by rw [det_kellerSegelJacobian]; positivity)
      (by rw [trace_kellerSegelDiffusion]; linarith)
      (by rw [det_kellerSegelDiffusion]; positivity),
    crossCoeff_kellerSegel, det_kellerSegelDiffusion, det_kellerSegelJacobian, mul_one]

/-- **Cross-diffusion-driven pattern formation in Keller–Segel.** For `r, β, d_u, d_v, α > 0`:
no diagonal diffusion (with any `d_u', d_v' ≥ 0`) destabilizes the Keller–Segel state
`(1, α / β)`, but chemotactic cross-diffusion with sensitivity
`χ > (2 √(d_u d_v r β) + r d_v + β d_u) / α` does. -/
theorem kellerSegel_crossDiffusionDriven {r α β du dv χ : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hβ : 0 < β) (hdu : 0 < du) (hdv : 0 < dv)
    (hχ : (2 * Real.sqrt (du * dv * (r * β)) + r * dv + β * du) / α < χ) :
    (∀ du' dv' : ℝ, 0 ≤ du' → 0 ≤ dv' →
      ¬ ∃ k, IsUnstableMode (kellerSegelJacobian r α β) du' dv' k) ∧
      ∃ k, IsCrossUnstableMode (kellerSegelJacobian r α β) (kellerSegelDiffusion du dv χ 1) k := by
  refine ⟨fun du' dv' hdu' hdv' => not_exists_isUnstableMode_of_nonpos
    (by rw [trace_kellerSegelJacobian]; linarith) (by rw [det_kellerSegelJacobian]; positivity)
    (by simp [kellerSegelJacobian]; linarith) (by simp [kellerSegelJacobian]; linarith) hdu' hdv',
    (kellerSegel_turing_iff hr hβ hdu hdv).2 ?_⟩
  rw [div_lt_iff₀ hα] at hχ
  linarith

/-- In the minimal Keller–Segel model (`r = 0`) every `(u₀, α u₀ / β)` is a steady state
(`β ≠ 0`). -/
theorem minimalKellerSegel_steadyState (α : ℝ) {β : ℝ} (hβ : β ≠ 0) (u₀ : ℝ) :
    kellerSegelKinetics 0 α β ![u₀, α * u₀ / β] = 0 := by
  funext i
  fin_cases i
  · simp [kellerSegelKinetics]
  · simp [kellerSegelKinetics]
    field_simp
    ring

/-- The minimal Keller–Segel kinetics are linear, so their Jacobian is
`kellerSegelJacobian 0 α β` at every state, in particular, for `β ≠ 0`, at each steady state
`(u₀, α u₀ / β)`. -/
theorem jacobianMatrix_minimalKellerSegel (α β : ℝ) (x : Fin 2 → ℝ) :
    MetaMathlibExt.jacobianMatrix (kellerSegelKinetics 0 α β) x = kellerSegelJacobian 0 α β := by
  have h0 : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add _
  have h1 : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      MetaMathlibExt.jacobianMatrix_apply, kellerSegelKinetics, Pi.add_apply, cons_val_zero,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, cons_val_one, cons_val_fin_one,
      ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero,
      add_zero, kellerSegelJacobian, of_apply, cons_val']
  · simp
  · simp
  · rw [((h0.const_mul α).sub_const (β * x 1)).deriv]
    ring
  · rw [((h1.const_mul β).const_sub (α * x 0)).deriv]
    ring

/-- The minimal Keller–Segel dispersion polynomial: with `r = 0`,
`h(k²) = k² (d_u d_v k² - (α χ u₀ - β d_u))`. -/
theorem crossDispersionDet_minimalKellerSegel (α β du dv χ u₀ k : ℝ) :
    crossDispersionDet (kellerSegelJacobian 0 α β) (kellerSegelDiffusion du dv χ u₀) (k ^ 2) =
      k ^ 2 * (du * dv * k ^ 2 - (α * χ * u₀ - β * du)) := by
  rw [crossDispersionDet, crossCoeff_kellerSegel, det_kellerSegelDiffusion,
    det_kellerSegelJacobian]
  ring

/-- **Chemotactic instability of the minimal Keller–Segel model.** For `β > 0` and
`d_u, d_v ≥ 0`, at any homogeneous cell density `u₀` (steady state `(u₀, α u₀ / β)` by
`minimalKellerSegel_steadyState`, Jacobian `kellerSegelJacobian 0 α β` by
`jacobianMatrix_minimalKellerSegel`, diffusion matrix by `kellerSegelFlux_add`) the mode
`k ≠ 0` is unstable iff `d_u d_v k² < α χ u₀ - β d_u`. -/
theorem minimalKellerSegel_isCrossUnstableMode_iff {α β du dv χ u₀ k : ℝ} (hβ : 0 < β)
    (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hk : k ≠ 0) :
    IsCrossUnstableMode (kellerSegelJacobian 0 α β) (kellerSegelDiffusion du dv χ u₀) k ↔
      du * dv * k ^ 2 < α * χ * u₀ - β * du := by
  rw [isCrossUnstableMode_iff_crossDispersionDet_neg
      (by rw [trace_kellerSegelJacobian]; linarith)
      (by rw [trace_kellerSegelDiffusion]; linarith),
    crossDispersionDet_minimalKellerSegel]
  have hk2 : 0 < k ^ 2 := by positivity
  constructor
  · intro h
    by_contra hc
    exact absurd h (not_lt.2 (mul_nonneg hk2.le (by linarith)))
  · intro h
    exact mul_neg_of_pos_of_neg hk2 (by linarith)

/-- For `β > 0`, in the minimal Keller–Segel model the homogeneous mode is not unstable (it is
neutral: `det J = 0`, mass conservation). -/
theorem minimalKellerSegel_not_isCrossUnstableMode_zero {α β : ℝ} (hβ : 0 < β)
    (D : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ IsCrossUnstableMode (kellerSegelJacobian 0 α β) D 0 := by
  rw [isCrossUnstableMode_iff, trace_crossModeMatrix, det_crossModeMatrix, crossDispersionDet,
    trace_kellerSegelJacobian, det_kellerSegelJacobian]
  push Not
  constructor <;> nlinarith

/-- **Minimal Keller–Segel on `[0, L]`.** With Neumann conditions, `β > 0`, `d_u, d_v ≥ 0` and
`0 < L`, some nonhomogeneous mode `cos(n π x / L)` (`n ≥ 1`) is unstable iff the first one is,
i.e. iff `d_u d_v (π / L)² < α χ u₀ - β d_u`. -/
theorem minimalKellerSegel_exists_neumann_iff {α β du dv χ u₀ L : ℝ} (hβ : 0 < β)
    (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hL : 0 < L) :
    (∃ n : ℕ, 0 < n ∧ IsCrossUnstableMode (kellerSegelJacobian 0 α β)
        (kellerSegelDiffusion du dv χ u₀) (neumannWavenumber L n)) ↔
      du * dv * (Real.pi / L) ^ 2 < α * χ * u₀ - β * du := by
  have hpl : 0 < Real.pi / L := div_pos Real.pi_pos hL
  constructor
  · rintro ⟨n, hn, h⟩
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hkn : Real.pi / L ≤ neumannWavenumber L n := by
      rw [neumannWavenumber, mul_div_assoc]
      nlinarith
    have hk0 : neumannWavenumber L n ≠ 0 := (lt_of_lt_of_le hpl hkn).ne'
    rw [minimalKellerSegel_isCrossUnstableMode_iff hβ hdu hdv hk0] at h
    have hsq : (Real.pi / L) ^ 2 ≤ neumannWavenumber L n ^ 2 := pow_le_pow_left₀ hpl.le hkn 2
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hdu hdv)]
  · intro h
    have hk1 : neumannWavenumber L 1 = Real.pi / L := by simp [neumannWavenumber]
    refine ⟨1, one_pos, ?_⟩
    rw [minimalKellerSegel_isCrossUnstableMode_iff hβ hdu hdv (hk1 ▸ hpl.ne'), hk1]
    exact h

end MathlibExt.Biology.Dynamics.TuringCrossDiffusion
