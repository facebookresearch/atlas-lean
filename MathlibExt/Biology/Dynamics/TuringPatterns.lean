/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Analysis.Calculus.Jacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Turing patterns: diffusion-driven instability of two-species reaction-diffusion systems

A two-species reaction-diffusion system on the line,

  `u_t = d_u u_xx + f(u, v)`,   `v_t = d_v v_xx + g(u, v)`,

with a spatially homogeneous steady state `(u₀, v₀)` (`f(u₀, v₀) = g(u₀, v₀) = 0`) is linearized
at that state to `w_t = D w_xx + J w`, where `J = [[f_u, f_v], [g_u, g_v]]` is the Jacobian of
the kinetics at `(u₀, v₀)` and `D = diag(d_u, d_v)` is the diffusion matrix. Substituting a
Fourier mode `w(t, x) = e^{μ t} cos(k x) v` turns the PDE into the eigenvalue problem
`(J - k² D) v = μ v` (the *dispersion relation*), so the mode of wavenumber `k` grows iff
`J - k² D` has an eigenvalue with positive real part. For a real `2 × 2` matrix this happens iff
its trace is positive or its determinant is negative.

Turing (1952) observed that diffusion can destabilize a state that is stable for the kinetics
alone. If `tr J < 0` and `det J > 0` (stability without diffusion) and `d_u, d_v ≥ 0`, then
`tr (J - k² D) < 0` for every `k`, so mode `k` is unstable iff

  `h(k²) := det (J - k² D) = d_u d_v k⁴ - (d_v f_u + d_u g_v) k² + det J < 0`.

Minimizing the quadratic `h` gives the algebraic criterion: some mode is unstable iff
`d_v f_u + d_u g_v > 2 √(d_u d_v det J)`; the minimum sits at the critical wavenumber
`k_c² = (d_v f_u + d_u g_v) / (2 d_u d_v)`. Consequently `f_u` and `g_v` have opposite signs,
and if `u` is the activator (`f_u > 0`) the inhibitor must diffuse faster (`d_u < d_v`).

On an interval `[0, L]` with homogeneous Neumann (zero-flux) boundary conditions the admissible
modes are `cos(k_n x)` with `k_n = n π / L`; mode `n` is unstable iff `k_n²` lies in the open
band where `h < 0`. Only finitely many modes are unstable, none if the domain is too small,
and, under Turing's criterion, some mode is unstable once the domain is large enough.

The Schnakenberg kinetics `f = a - u + u² v`, `g = b - u² v` have the steady state
`(a + b, b / (a + b)²)`, which is stable without diffusion iff `b - a < (a + b)³`; with
`d_u = 1`, `d_v = d` such a state is Turing-unstable iff `d (b - a) - (a + b)³ > 2 √d (a + b)²`
(Murray 2003, ch. 2). The Gierer–Meinhardt kinetics in Murray's nondimensional form
`f = a - b u + u² / v`, `g = u² - v` have the steady state `((a + 1) / b, ((a + 1) / b)²)`,
which is stable without diffusion iff `b (1 - a) < 1 + a` and Turing-unstable iff
`d b (1 - a) / (1 + a) - 1 > 2 √(d b)`.

Rates and diffusion coefficients are dimensionless; time and space are in the units of the
nondimensionalized system. Only the *linear* analysis is formalized: the linearization principle
(that linear instability of the PDE implies nonlinear instability, and the selection of the
final pattern) is not covered.

## Main results

* `exists_eigenvalue_re_pos_iff`: a real `2 × 2` matrix has a (complex) eigenvalue with positive
  real part iff `0 < tr M ∨ det M < 0`.
* `fourierMode_isLinearizedSolution_iff`: the dispersion relation — the Fourier mode
  `e^{μ t} cos(k x) v` solves `w_t = D w_xx + J w` iff `(J - k² D) v = μ v`.
* `isUnstableMode_iff_exists_growing`: `J - k² D` has an eigenvalue with positive real part iff
  some nonzero Fourier mode of wavenumber `k` solves the linearized system and grows without
  bound.
* `turing_instability`: stability without diffusion plus `det (J - k² D) < 0` gives a stable
  homogeneous mode and an unstable mode `k`.
* `exists_isUnstableMode_iff`: Turing's algebraic criterion
  `d_v f_u + d_u g_v > 2 √(d_u d_v det J)`.
* `dispersionDet_criticalWavenumberSq_le`, `isUnstableMode_sqrt_criticalWavenumberSq`: the
  critical wavenumber minimizes `h` and is unstable under Turing's criterion.
* `mul_neg_of_exists_isUnstableMode`, `lt_of_exists_isUnstableMode`: `f_u g_v < 0`, and an
  activator (`f_u > 0`) forces `d_u < d_v`.
* `isUnstableMode_neumannWavenumber_iff`, `finite_setOf_isUnstableMode_neumannWavenumber`,
  `not_isUnstableMode_neumannWavenumber_of_le`, `exists_isUnstableMode_neumannWavenumber`:
  Neumann modes on `[0, L]`.
* `jacobianMatrix_schnakenberg`, `schnakenberg_turing_iff`: the Schnakenberg kinetics.
* `jacobianMatrix_giererMeinhardt`, `giererMeinhardt_turing_iff`: the Gierer–Meinhardt kinetics.

## References

* A. M. Turing, *The chemical basis of morphogenesis*, Phil. Trans. R. Soc. Lond. B 237 (1952)
  37–72.
* A. Gierer and H. Meinhardt, *A theory of biological pattern formation*, Kybernetik 12 (1972)
  30–39.
* J. Schnakenberg, *Simple chemical reaction systems with limit cycle behaviour*, J. Theor. Biol.
  81 (1979) 389–400.
* J. D. Murray, *Mathematical Biology II: Spatial Models and Biomedical Applications*, 3rd ed.,
  Springer (2003), ch. 2.
* L. Edelstein-Keshet, *Mathematical Models in Biology*, Random House (1988).
-/

@[expose] public section

open Matrix Filter Topology

namespace MathlibExt.Biology.Dynamics.TuringPatterns

/-- The diffusion matrix `D = diag(d_u, d_v)` of a two-species reaction-diffusion system. -/
def diffusionMatrix (du dv : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![du, dv]

/-- The mode matrix `J - k² D` governing the Fourier mode of wavenumber `k` of the linearized
system `w_t = D w_xx + J w`, where `J` is the Jacobian of the kinetics at the steady state
(convention: `J i j` is the partial derivative of the `i`-th reaction term with respect to the
`j`-th species, so `J = [[f_u, f_v], [g_u, g_v]]`). -/
def modeMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  J - k ^ 2 • diffusionMatrix du dv

/-- The Fourier mode of wavenumber `k` is *linearly unstable*: the mode matrix `J - k² D` has
a complex eigenvalue `μ` with `0 < Re μ`. -/
def IsUnstableMode (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ) : Prop :=
  ∃ μ : ℂ, 0 < μ.re ∧ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
    (modeMatrix J du dv k).map (↑) *ᵥ v = μ • v

/-- The complex Fourier mode `w(t, x) = e^{μ t} cos(k x) v` with growth rate `μ`, wavenumber `k`
and amplitude vector `v`. (The real part of a complex solution of the real linear system is a
real solution.) -/
noncomputable def fourierMode (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ) (t x : ℝ) : Fin 2 → ℂ :=
  (Complex.exp (μ * t) * (Real.cos (k * x) : ℂ)) • v

/-- `w` is a classical solution of the linearized reaction-diffusion system
`w_t = D w_xx + J w` on `ℝ × ℝ`: `w(t, ·)` is twice differentiable with first and second
derivatives `wx`, `wxx`, and `w(·, x)` is differentiable with the prescribed time derivative. -/
def IsLinearizedSolution (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ)
    (w : ℝ → ℝ → Fin 2 → ℂ) : Prop :=
  ∃ wx wxx : ℝ → ℝ → Fin 2 → ℂ, ∀ t x,
    HasDerivAt (w t) (wx t x) x ∧ HasDerivAt (wx t) (wxx t x) x ∧
    HasDerivAt (fun s => w s x)
      ((diffusionMatrix du dv).map (↑) *ᵥ wxx t x + J.map (↑) *ᵥ w t x) t

/-- The dispersion polynomial `h(q) = d_u d_v q² - (d_v f_u + d_u g_v) q + det J`, so that
`det (J - k² D) = h(k²)` (`det_modeMatrix`). -/
def dispersionDet (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv q : ℝ) : ℝ :=
  du * dv * q ^ 2 - (dv * J 0 0 + du * J 1 1) * q + J.det

/-- The squared critical wavenumber `k_c² = (d_v f_u + d_u g_v) / (2 d_u d_v)`, the minimizer
of the dispersion polynomial (meaningful for `d_u, d_v > 0`; division by zero gives `0`). -/
noncomputable def criticalWavenumberSq (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ) : ℝ :=
  (dv * J 0 0 + du * J 1 1) / (2 * du * dv)

/-- The discriminant `(d_v f_u + d_u g_v)² - 4 d_u d_v det J` of the dispersion polynomial. -/
def bandDiscriminant (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ) : ℝ :=
  (dv * J 0 0 + du * J 1 1) ^ 2 - 4 * du * dv * J.det

/-- Lower end `q₋ = (S - √Δ) / (2 d_u d_v)` of the unstable band of squared wavenumbers, where
`S = d_v f_u + d_u g_v` and `Δ = bandDiscriminant` (meaningful when `0 < Δ`, `d_u, d_v > 0`). -/
noncomputable def bandLower (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ) : ℝ :=
  (dv * J 0 0 + du * J 1 1 - Real.sqrt (bandDiscriminant J du dv)) / (2 * du * dv)

/-- Upper end `q₊ = (S + √Δ) / (2 d_u d_v)` of the unstable band of squared wavenumbers
(meaningful when `0 < Δ`, `d_u, d_v > 0`). -/
noncomputable def bandUpper (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv : ℝ) : ℝ :=
  (dv * J 0 0 + du * J 1 1 + Real.sqrt (bandDiscriminant J du dv)) / (2 * du * dv)

/-- The Neumann wavenumber `k_n = n π / L` of the mode `cos(n π x / L)` on `[0, L]`.
Meaningful only for `0 < L`; at `L = 0` the totalized division gives `0`, so every
labeled Neumann mode collapses to the homogeneous mode. -/
noncomputable def neumannWavenumber (L : ℝ) (n : ℕ) : ℝ :=
  n * Real.pi / L

/-! ### The dispersion relation -/

/-- `tr (J - k² D) = tr J - k² (d_u + d_v)`. -/
theorem trace_modeMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ) :
    (modeMatrix J du dv k).trace = J.trace - k ^ 2 * (du + dv) := by
  simp [modeMatrix, diffusionMatrix, Matrix.trace_fin_two]

/-- `det (J - k² D) = h(k²)`. -/
theorem det_modeMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ) :
    (modeMatrix J du dv k).det = dispersionDet J du dv (k ^ 2) := by
  simp [modeMatrix, dispersionDet, diffusionMatrix, Matrix.det_fin_two]
  ring

/-- **Routh–Hurwitz for `2 × 2` matrices.** A real `2 × 2` matrix has a complex eigenvalue with
positive real part iff its trace is positive or its determinant is negative. -/
theorem exists_eigenvalue_re_pos_iff (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ μ : ℂ, 0 < μ.re ∧ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = μ • v) ↔
      0 < M.trace ∨ M.det < 0 := by
  classical
  have eigen_iff (μ : ℂ) :
      (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = μ • v) ↔
        μ ^ 2 - (M.trace : ℂ) * μ + (M.det : ℂ) = 0 := by
    have hdet : (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M.map Complex.ofReal).det =
        μ ^ 2 - (M.trace : ℂ) * μ + (M.det : ℂ) := by
      simp [Matrix.det_fin_two, Matrix.trace_fin_two,
        Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply]
      ring
    rw [← hdet, ← Matrix.exists_mulVec_eq_zero_iff]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero, eq_comm]
  simp_rw [eigen_iff]
  constructor
  · rintro ⟨μ, hpos, hroot⟩
    have hre := congrArg Complex.re hroot
    have him := congrArg Complex.im hroot
    simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul, sub_zero] at hre
    simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im, zero_mul, add_zero] at him
    by_cases hb : μ.im = 0
    · rw [hb] at hre
      by_cases ht : 0 < M.trace
      · exact Or.inl ht
      · right
        have ht' : M.trace ≤ 0 := le_of_not_gt ht
        nlinarith [mul_nonpos_of_nonpos_of_nonneg ht' (le_of_lt hpos)]
    · left
      have hfactor : μ.im * (2 * μ.re - M.trace) = 0 := by nlinarith [him]
      have ht := (mul_eq_zero.mp hfactor).resolve_left hb
      linarith
  · intro h
    by_cases hd : 0 ≤ M.trace ^ 2 - 4 * M.det
    · let s := Real.sqrt (M.trace ^ 2 - 4 * M.det)
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = M.trace ^ 2 - 4 * M.det := Real.sq_sqrt hd
      have hpos : 0 < (M.trace + s) / 2 := by
        rcases h with ht | hdet
        · linarith
        · have hlt : -M.trace < s := by
            by_contra hle
            have hle' : s ≤ -M.trace := le_of_not_gt hle
            nlinarith [sq_nonneg (s + M.trace)]
          linarith
      refine ⟨((M.trace + s) / 2 : ℝ), ?_, ?_⟩
      · exact hpos
      · apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
        nlinarith [hs2]
    · have hd' : 0 ≤ 4 * M.det - M.trace ^ 2 := by linarith
      have ht : 0 < M.trace := by
        rcases h with ht | hdet
        · exact ht
        · nlinarith [sq_nonneg M.trace]
      let s := Real.sqrt (4 * M.det - M.trace ^ 2)
      have hs2 : s ^ 2 = 4 * M.det - M.trace ^ 2 := Real.sq_sqrt hd'
      refine ⟨⟨M.trace / 2, s / 2⟩, by dsimp; linarith, ?_⟩
      apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
      · nlinarith [hs2]
      · ring

/-- Mode `k` is unstable iff `0 < tr (J - k² D)` or `det (J - k² D) < 0`. -/
theorem isUnstableMode_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ} :
    IsUnstableMode J du dv k ↔
      0 < (modeMatrix J du dv k).trace ∨ (modeMatrix J du dv k).det < 0 :=
  exists_eigenvalue_re_pos_iff _

/-- The `x`-derivative of the Fourier mode: `-k e^{μ t} sin(k x) v`. -/
private theorem fourierMode_hasDerivAt_space (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ)
    (t x : ℝ) :
    HasDerivAt (fourierMode μ k v t)
      ((Complex.exp (μ * t) * ((-k * Real.sin (k * x) : ℝ) : ℂ)) • v) x := by
  change HasDerivAt
    (fun y => (Complex.exp (μ * t) * (Real.cos (k * y) : ℂ)) • v) _ x
  have h := (Real.hasDerivAt_cos (k * x)).comp x ((hasDerivAt_id x).const_mul k)
  simpa [fourierMode, mul_comm, mul_left_comm, mul_assoc] using
    (h.ofReal_comp.const_mul (Complex.exp (μ * t))).smul_const v

/-- The second `x`-derivative of the Fourier mode: `-k² e^{μ t} cos(k x) v`. -/
private theorem fourierMode_hasDerivAt_space_second (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ)
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

/-- The `t`-derivative of the Fourier mode: `μ e^{μ t} cos(k x) v`. -/
private theorem fourierMode_hasDerivAt_time (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ)
    (t x : ℝ) :
    HasDerivAt (fun s => fourierMode μ k v s x)
      ((μ * Complex.exp (μ * t) * (Real.cos (k * x) : ℂ)) • v) t := by
  simpa [fourierMode, mul_comm, mul_left_comm, mul_assoc] using
    ((((hasDerivAt_id t).ofReal_comp.const_mul μ).cexp).mul_const
      (Real.cos (k * x) : ℂ)).smul_const v

/-- `D (-k² v) + J v = (J - k² D) v` over `ℂ`. -/
private theorem modeMatrix_mulVec (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ)
    (v : Fin 2 → ℂ) :
    (diffusionMatrix du dv).map (↑) *ᵥ (-(k : ℂ) ^ 2 • v) + J.map (↑) *ᵥ v =
      (modeMatrix J du dv k).map (↑) *ᵥ v := by
  funext i
  simp [modeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- **Dispersion relation.** The Fourier mode `e^{μ t} cos(k x) v` is a classical solution of
the linearized system `w_t = D w_xx + J w` iff `(J - k² D) v = μ v`. -/
theorem fourierMode_isLinearizedSolution_iff (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ)
    (μ : ℂ) (v : Fin 2 → ℂ) :
    IsLinearizedSolution J du dv (fourierMode μ k v) ↔
      (modeMatrix J du dv k).map (↑) *ᵥ v = μ • v := by
  constructor
  · rintro ⟨wx, wxx, h⟩
    have hwx : wx 0 = fun x =>
        (Complex.exp (μ * 0) * ((-k * Real.sin (k * x) : ℝ) : ℂ)) • v := by
      funext x
      exact (h 0 x).1.unique (fourierMode_hasDerivAt_space μ k v 0 x)
    have hwxx := (h 0 0).2.1
    rw [hwx] at hwxx
    have hsecond := hwxx.unique (fourierMode_hasDerivAt_space_second μ k v 0 0)
    have htime := (h 0 0).2.2.unique (fourierMode_hasDerivAt_time μ k v 0 0)
    simp only [mul_zero, Real.cos_zero, Complex.ofReal_one, mul_one, Complex.ofReal_neg,
      Complex.ofReal_pow] at hsecond htime
    rw [hsecond] at htime
    simpa [fourierMode, ← modeMatrix_mulVec J du dv k v] using htime
  · intro h
    refine ⟨(fun t x =>
      (Complex.exp (μ * t) * ((-k * Real.sin (k * x) : ℝ) : ℂ)) • v),
      (fun t x => (Complex.exp (μ * t) * ((-k ^ 2 * Real.cos (k * x) : ℝ) : ℂ)) • v),
      ?_⟩
    intro t x
    refine ⟨fourierMode_hasDerivAt_space μ k v t x,
      fourierMode_hasDerivAt_space_second μ k v t x, ?_⟩
    have hbase := (modeMatrix_mulVec J du dv k v).trans h
    have hpde : (diffusionMatrix du dv).map (↑) *ᵥ
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
    exact fourierMode_hasDerivAt_time μ k v t x

/-- The amplitude of a Fourier mode: `‖w(t, 0)‖ = e^{Re μ · t} ‖v‖`. -/
theorem norm_fourierMode_zero (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ) (t : ℝ) :
    ‖fourierMode μ k v t 0‖ = Real.exp (μ.re * t) * ‖v‖ := by
  simp [fourierMode, norm_smul, Complex.norm_exp, Complex.mul_re]

/-- `‖w(t, 0)‖` is the amplitude of the mode: `‖w(t, x)‖ ≤ ‖w(t, 0)‖` for every `x`. -/
theorem norm_fourierMode_le (μ : ℂ) (k : ℝ) (v : Fin 2 → ℂ) (t x : ℝ) :
    ‖fourierMode μ k v t x‖ ≤ ‖fourierMode μ k v t 0‖ := by
  rw [norm_fourierMode_zero]
  simp only [fourierMode, norm_smul, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) (norm_nonneg _)

/-- A nonzero Fourier mode grows without bound iff its growth rate has positive real part. -/
theorem tendsto_norm_fourierMode_iff {v : Fin 2 → ℂ} (hv : v ≠ 0) (μ : ℂ) (k : ℝ) :
    Tendsto (fun t => ‖fourierMode μ k v t 0‖) atTop atTop ↔ 0 < μ.re := by
  simp_rw [norm_fourierMode_zero]
  rw [tendsto_mul_const_atTop_of_pos (norm_pos_iff.mpr hv), Real.tendsto_exp_comp_atTop]
  exact tendsto_const_mul_atTop_iff_pos tendsto_id

/-- **A Fourier mode grows iff `J - k² D` has an eigenvalue with positive real part.** -/
theorem isUnstableMode_iff_exists_growing {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ} :
    IsUnstableMode J du dv k ↔ ∃ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      IsLinearizedSolution J du dv (fourierMode μ k v) ∧
      Tendsto (fun t => ‖fourierMode μ k v t 0‖) atTop atTop := by
  constructor
  · rintro ⟨μ, hμ, v, hv, h⟩
    exact ⟨μ, v, hv, (fourierMode_isLinearizedSolution_iff J du dv k μ v).2 h,
      (tendsto_norm_fourierMode_iff hv μ k).2 hμ⟩
  · rintro ⟨μ, v, hv, hsol, hgrow⟩
    exact ⟨μ, (tendsto_norm_fourierMode_iff hv μ k).1 hgrow, v, hv,
      (fourierMode_isLinearizedSolution_iff J du dv k μ v).1 hsol⟩

/-! ### Diffusion-driven instability -/

/-- The homogeneous mode `k = 0` is stable when the kinetics are stable (`tr J < 0`,
`0 < det J`). -/
theorem not_isUnstableMode_zero {J : Matrix (Fin 2) (Fin 2) ℝ} (htr : J.trace < 0)
    (hdet : 0 < J.det) (du dv : ℝ) : ¬ IsUnstableMode J du dv 0 := by
  rw [isUnstableMode_iff, trace_modeMatrix, det_modeMatrix]
  simp only [dispersionDet]
  push Not
  constructor <;> nlinarith

/-- If `tr J < 0` and `d_u, d_v ≥ 0`, mode `k` is unstable iff `h(k²) < 0`. -/
theorem isUnstableMode_iff_dispersionDet_neg {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (htr : J.trace < 0) (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (k : ℝ) :
    IsUnstableMode J du dv k ↔ dispersionDet J du dv (k ^ 2) < 0 := by
  rw [isUnstableMode_iff, trace_modeMatrix, det_modeMatrix]
  have : J.trace - k ^ 2 * (du + dv) < 0 := by nlinarith [sq_nonneg k]
  constructor
  · rintro (h | h)
    · linarith
    · exact h
  · exact Or.inr

/-- **Diffusion-driven instability (Turing 1952).** If the steady state is stable without
diffusion (`tr J < 0`, `0 < det J`), `d_u, d_v ≥ 0`, and `det (J - k² D) < 0`, then the
homogeneous mode is stable while mode `k` is unstable. -/
theorem turing_instability {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ} (htr : J.trace < 0)
    (hdet : 0 < J.det) (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hk : (modeMatrix J du dv k).det < 0) :
    ¬ IsUnstableMode J du dv 0 ∧ IsUnstableMode J du dv k :=
  ⟨not_isUnstableMode_zero htr hdet du dv,
    (isUnstableMode_iff_dispersionDet_neg htr hdu hdv k).2 (det_modeMatrix J du dv k ▸ hk)⟩

/-- The value of the dispersion polynomial at its minimizer:
`h(k_c²) = det J - (d_v f_u + d_u g_v)² / (4 d_u d_v)`. -/
theorem dispersionDet_criticalWavenumberSq {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) :
    dispersionDet J du dv (criticalWavenumberSq J du dv) =
      J.det - (dv * J 0 0 + du * J 1 1) ^ 2 / (4 * du * dv) := by
  unfold dispersionDet criticalWavenumberSq
  field_simp
  ring

/-- The critical squared wavenumber minimizes the dispersion polynomial over all real `q`. -/
theorem dispersionDet_criticalWavenumberSq_le {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (q : ℝ) :
    dispersionDet J du dv (criticalWavenumberSq J du dv) ≤ dispersionDet J du dv q := by
  have h : dispersionDet J du dv q - dispersionDet J du dv (criticalWavenumberSq J du dv) =
      du * dv * (q - criticalWavenumberSq J du dv) ^ 2 := by
    unfold dispersionDet criticalWavenumberSq
    field_simp
    ring
  nlinarith [mul_nonneg (mul_pos hdu hdv).le (sq_nonneg (q - criticalWavenumberSq J du dv))]

/-- The Turing condition in squared form: `2 √(d_u d_v det J) < S` iff `0 < S` and
`4 d_u d_v det J < S²`, where `S = d_v f_u + d_u g_v`. This holds for all real inputs: when
`d_u d_v det J < 0`, `Real.sqrt` returns `0` and both sides reduce to `0 < S`. -/
theorem two_mul_sqrt_lt_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ} :
    2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1 ↔
      0 < dv * J 0 0 + du * J 1 1 ∧ 4 * du * dv * J.det < (dv * J 0 0 + du * J 1 1) ^ 2 := by
  constructor
  · intro h
    have hS : 0 < dv * J 0 0 + du * J 1 1 :=
      lt_of_le_of_lt (by positivity) h
    refine ⟨hS, ?_⟩
    have := (Real.sqrt_lt' (x := du * dv * J.det)
      (by linarith : 0 < (dv * J 0 0 + du * J 1 1) / 2)).1 (by linarith)
    nlinarith
  · rintro ⟨hS, h⟩
    have := (Real.sqrt_lt' (x := du * dv * J.det) (half_pos hS)).2 (by nlinarith)
    linarith

/-- For `d_u, d_v > 0` and `0 < det J`, the dispersion polynomial is negative at some
`q ≥ 0` iff `2 √(d_u d_v det J) < d_v f_u + d_u g_v`. -/
theorem exists_dispersionDet_neg_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (hdet : 0 < J.det) :
    (∃ q, 0 ≤ q ∧ dispersionDet J du dv q < 0) ↔
      2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1 := by
  rw [two_mul_sqrt_lt_iff]
  let A := du * dv
  let S := dv * J 0 0 + du * J 1 1
  let C := J.det
  have hA : 0 < A := mul_pos hdu hdv
  change (∃ q, 0 ≤ q ∧ A * q ^ 2 - S * q + C < 0) ↔
    0 < S ∧ 4 * du * dv * C < S ^ 2
  have hC : 0 < C := hdet
  constructor
  · rintro ⟨q, hq, hneg⟩
    have hS : 0 < S := by
      by_contra h
      have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hq
      have hquad := mul_nonneg hA.le (sq_nonneg q)
      nlinarith
    have hid : 4 * A * (A * q ^ 2 - S * q + C) =
        (2 * A * q - S) ^ 2 - (S ^ 2 - 4 * A * C) := by ring
    have hmul := mul_neg_of_pos_of_neg (show 0 < 4 * A by positivity) hneg
    refine ⟨hS, ?_⟩
    dsimp [A] at hid hmul
    nlinarith only [hid, hmul, sq_nonneg (2 * A * q - S)]
  · rintro ⟨hS, hsq⟩
    have hden : 0 < 2 * A := by positivity
    have hden4 : 0 < 4 * A := by positivity
    refine ⟨S / (2 * A), (div_pos hS hden).le, ?_⟩
    have hid : A * (S / (2 * A)) ^ 2 - S * (S / (2 * A)) + C =
        (4 * A * C - S ^ 2) / (4 * A) := by
      field_simp
      ring
    rw [hid]
    apply div_neg_of_neg_of_pos _ hden4
    dsimp [A] at hA ⊢
    nlinarith only [hsq]

/-- **Turing's criterion.** If the steady state is stable without diffusion
(`tr J < 0`, `0 < det J`) and `d_u, d_v > 0`, some Fourier mode is unstable iff
`d_v f_u + d_u g_v > 2 √(d_u d_v det J)`. -/
theorem exists_isUnstableMode_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ} (hdu : 0 < du)
    (hdv : 0 < dv) (htr : J.trace < 0) (hdet : 0 < J.det) :
    (∃ k, IsUnstableMode J du dv k) ↔
      2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1 := by
  rw [← exists_dispersionDet_neg_iff hdu hdv hdet]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k ^ 2, sq_nonneg k,
      (isUnstableMode_iff_dispersionDet_neg htr hdu.le hdv.le k).1 hk⟩
  · rintro ⟨q, hq, h⟩
    refine ⟨Real.sqrt q, (isUnstableMode_iff_dispersionDet_neg htr hdu.le hdv.le _).2 ?_⟩
    rwa [Real.sq_sqrt hq]

/-- Under Turing's criterion the critical wavenumber `k_c = √(k_c²)` is itself unstable (and
`0 < k_c²`). -/
theorem isUnstableMode_sqrt_criticalWavenumberSq {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (_hdet : 0 < J.det)
    (h : 2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1) :
    0 < criticalWavenumberSq J du dv ∧
      IsUnstableMode J du dv (Real.sqrt (criticalWavenumberSq J du dv)) := by
  obtain ⟨hS, hsq⟩ := two_mul_sqrt_lt_iff.1 h
  have hq : 0 < criticalWavenumberSq J du dv := by
    unfold criticalWavenumberSq
    positivity
  refine ⟨hq, (isUnstableMode_iff_dispersionDet_neg htr hdu.le hdv.le _).2 ?_⟩
  rw [Real.sq_sqrt hq.le, dispersionDet_criticalWavenumberSq hdu hdv, sub_neg,
    lt_div_iff₀ (by positivity)]
  linarith

/-- At the bifurcation threshold `d_v f_u + d_u g_v = 2 √(d_u d_v det J)` the critical
squared wavenumber is `k_c² = √(det J / (d_u d_v))` and `h(k_c²) = 0`. -/
theorem criticalWavenumberSq_of_threshold {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (hdet : 0 ≤ J.det)
    (h : dv * J 0 0 + du * J 1 1 = 2 * Real.sqrt (du * dv * J.det)) :
    criticalWavenumberSq J du dv = Real.sqrt (J.det / (du * dv)) ∧
      dispersionDet J du dv (criticalWavenumberSq J du dv) = 0 := by
  have hp : 0 < du * dv := mul_pos hdu hdv
  have hs : Real.sqrt (J.det / (du * dv)) = Real.sqrt (du * dv * J.det) / (du * dv) := by
    rw [show J.det / (du * dv) = du * dv * J.det / (du * dv) ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp.le]
  refine ⟨?_, ?_⟩
  · rw [hs, criticalWavenumberSq, h]
    field_simp
  · rw [dispersionDet_criticalWavenumberSq hdu hdv, h, mul_pow,
      Real.sq_sqrt (by positivity)]
    field_simp
    ring

/-- Diffusion-driven instability of a kinetically stable state forces
`0 < d_v f_u + d_u g_v`. -/
private theorem sum_pos_of_exists_isUnstableMode {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (htr : J.trace < 0) (hdet : 0 < J.det) (hdu : 0 ≤ du) (hdv : 0 ≤ dv)
    (h : ∃ k, IsUnstableMode J du dv k) : 0 < dv * J 0 0 + du * J 1 1 := by
  obtain ⟨k, hk⟩ := h
  have h' := (isUnstableMode_iff_dispersionDet_neg htr hdu hdv k).1 hk
  unfold dispersionDet at h'
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (mul_nonneg hdu hdv) (sq_nonneg (k ^ 2)),
    mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg k)]

/-- **`f_u` and `g_v` have opposite signs.** If the steady state is stable without diffusion
and `d_u, d_v ≥ 0`, diffusion-driven instability forces `f_u g_v < 0`. -/
theorem mul_neg_of_exists_isUnstableMode {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (htr : J.trace < 0) (hdet : 0 < J.det) (hdu : 0 ≤ du) (hdv : 0 ≤ dv)
    (h : ∃ k, IsUnstableMode J du dv k) : J 0 0 * J 1 1 < 0 := by
  have hS := sum_pos_of_exists_isUnstableMode htr hdet hdu hdv h
  rw [Matrix.trace_fin_two] at htr
  by_contra hc
  push Not at hc
  rcases lt_trichotomy (J 0 0) 0 with h0 | h0 | h0
  · have : J 1 1 ≤ 0 := by nlinarith
    nlinarith [mul_nonneg hdv (neg_nonneg.2 h0.le), mul_nonneg hdu (neg_nonneg.2 this)]
  · rw [h0] at hS htr
    nlinarith
  · have : 0 ≤ J 1 1 := by nlinarith
    linarith

/-- **The inhibitor diffuses faster.** In the activator-inhibitor sign pattern (`u` is the
activator, `0 < f_u`; then `g_v < 0` follows from `tr J < 0`), diffusion-driven instability of a
kinetically stable state forces `d_u < d_v`. -/
theorem lt_of_exists_isUnstableMode {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (htr : J.trace < 0) (hdet : 0 < J.det) (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hfu : 0 < J 0 0)
    (h : ∃ k, IsUnstableMode J du dv k) : du < dv := by
  have hS := sum_pos_of_exists_isUnstableMode htr hdet hdu hdv h
  rw [Matrix.trace_fin_two] at htr
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_right hc hfu.le, mul_nonpos_of_nonneg_of_nonpos hdu htr.le]

/-! ### Unstable band and finite domains -/

/-- For `d_u, d_v > 0`, the dispersion polynomial is negative exactly on the open band
`(q₋, q₊)`, which is nonempty iff the discriminant is positive. -/
theorem dispersionDet_neg_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ} (hdu : 0 < du)
    (hdv : 0 < dv) (q : ℝ) :
    dispersionDet J du dv q < 0 ↔
      0 < bandDiscriminant J du dv ∧ bandLower J du dv < q ∧ q < bandUpper J du dv := by
  let A := du * dv
  let S := dv * J 0 0 + du * J 1 1
  let C := J.det
  let D := bandDiscriminant J du dv
  let x := 2 * A * q - S
  have hA : 0 < A := mul_pos hdu hdv
  have hden : 0 < 2 * A := by positivity
  have hid : 4 * A * dispersionDet J du dv q = x ^ 2 - D := by
    dsimp [dispersionDet, bandDiscriminant, A, S, C, D, x]
    ring
  change dispersionDet J du dv q < 0 ↔
    0 < D ∧ (S - Real.sqrt D) / (2 * du * dv) < q ∧
      q < (S + Real.sqrt D) / (2 * du * dv)
  have hden' : 2 * du * dv = 2 * A := by dsimp [A]; ring
  rw [hden', div_lt_iff₀ hden, lt_div_iff₀ hden]
  have hr := Real.sqrt_nonneg D
  constructor
  · intro hneg
    have hmul := mul_neg_of_pos_of_neg (show 0 < 4 * A by positivity) hneg
    have hD : 0 < D := by nlinarith only [hid, hmul, sq_nonneg x]
    have hs := Real.sq_sqrt hD.le
    have hxs : x ^ 2 < (Real.sqrt D) ^ 2 := by nlinarith only [hid, hmul, hs]
    have hlo : -Real.sqrt D < x := by nlinarith only [hxs, hr]
    have hhi : x < Real.sqrt D := by nlinarith only [hxs, hr]
    refine ⟨hD, ?_, ?_⟩ <;> dsimp [x] at hlo hhi <;> linarith
  · rintro ⟨hD, hlo, hhi⟩
    have hs := Real.sq_sqrt hD.le
    have hxlo : -Real.sqrt D < x := by dsimp [x]; linarith
    have hxhi : x < Real.sqrt D := by dsimp [x]; linarith
    have hxs : x ^ 2 < D := by nlinarith only [hxlo, hxhi, hs]
    have hmul : 4 * A * dispersionDet J du dv q < 0 := by
      nlinarith only [hid, hxs]
    have hfactor : 0 < 4 * A := by positivity
    nlinarith only [hmul, hfactor]

/-- The Neumann mode `cos(k_n x)` has zero flux at both ends of `[0, L]`: the `x`-derivative of
the Fourier mode with wavenumber `k_n = n π / L` vanishes at `x = 0` and `x = L`. -/
theorem hasDerivAt_fourierMode_neumannWavenumber {L : ℝ} (hL : L ≠ 0) (n : ℕ) (μ : ℂ)
    (v : Fin 2 → ℂ) (t : ℝ) :
    HasDerivAt (fourierMode μ (neumannWavenumber L n) v t) 0 0 ∧
      HasDerivAt (fourierMode μ (neumannWavenumber L n) v t) 0 L := by
  constructor
  · simpa using fourierMode_hasDerivAt_space μ (neumannWavenumber L n) v t 0
  · have hk : neumannWavenumber L n * L = n * Real.pi := by
      unfold neumannWavenumber
      exact div_mul_cancel₀ _ hL
    simpa [hk, Real.sin_nat_mul_pi] using
      fourierMode_hasDerivAt_space μ (neumannWavenumber L n) v t L

/-- **Finite domain.** On `[0, L]` with Neumann boundary conditions, if `tr J < 0` and
`d_u, d_v > 0`, mode `n` is unstable iff `k_n² = (n π / L)²` lies in the unstable band
`(q₋, q₊)` (which requires a positive discriminant). -/
theorem isUnstableMode_neumannWavenumber_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (_hL : 0 < L) (n : ℕ) :
    IsUnstableMode J du dv (neumannWavenumber L n) ↔
      0 < bandDiscriminant J du dv ∧ bandLower J du dv < (n * Real.pi / L) ^ 2 ∧
        (n * Real.pi / L) ^ 2 < bandUpper J du dv := by
  rw [isUnstableMode_iff_dispersionDet_neg htr hdu.le hdv.le, dispersionDet_neg_iff hdu hdv]
  rfl

/-- Only finitely many Neumann modes are unstable on `[0, L]` (for `d_u, d_v, L > 0`, any `J`). -/
theorem finite_setOf_isUnstableMode_neumannWavenumber {J : Matrix (Fin 2) (Fin 2) ℝ}
    {du dv L : ℝ} (hdu : 0 < du) (hdv : 0 < dv) (hL : 0 < L) :
    {n : ℕ | IsUnstableMode J du dv (neumannWavenumber L n)}.Finite := by
  set S := dv * J 0 0 + du * J 1 1
  set Q := |J.trace| / (du + dv) + (|S| + |J.det|) / (du * dv) + 1 with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ |J.trace| / (du + dv) := by positivity
    have : 0 ≤ (|S| + |J.det|) / (du * dv) := by positivity
    linarith
  refine (Finset.range ⌈Q * L / Real.pi⌉₊).finite_toSet.subset fun n hn => ?_
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  push Not at hge
  have hn' : Q * L / Real.pi ≤ n := (Nat.ceil_le).1 hge
  have hk : Q ≤ n * Real.pi / L := by
    rw [div_le_iff₀ Real.pi_pos] at hn'
    rw [le_div_iff₀ hL]
    linarith
  set q := (neumannWavenumber L n) ^ 2
  have hq : Q ≤ q := by
    have : Q ≤ neumannWavenumber L n := hk
    simp only [q]
    nlinarith
  have hq1 : 1 ≤ q := le_trans hQ1 hq
  have htr : J.trace - q * (du + dv) ≤ 0 := by
    have h1 : |J.trace| / (du + dv) ≤ q := by
      have : 0 ≤ (|S| + |J.det|) / (du * dv) := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith [le_abs_self J.trace]
  have hdet : 0 ≤ dispersionDet J du dv q := by
    have h1 : (|S| + |J.det|) / (du * dv) ≤ q := by
      have : 0 ≤ |J.trace| / (du + dv) := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    unfold dispersionDet
    nlinarith [le_abs_self S, neg_abs_le J.det, abs_nonneg S, abs_nonneg J.det]
  rw [Set.mem_ofPred_eq, isUnstableMode_iff, trace_modeMatrix, det_modeMatrix] at hn
  rcases hn with h | h <;> linarith

/-- **Small domains admit no pattern.** If the first nonhomogeneous mode already lies beyond the
band, `q₊ ≤ (π / L)²`, then no Neumann mode is unstable on `[0, L]`. -/
theorem not_isUnstableMode_neumannWavenumber_of_le {J : Matrix (Fin 2) (Fin 2) ℝ}
    {du dv L : ℝ} (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (hdet : 0 < J.det)
    (hL : 0 < L) (hsmall : bandUpper J du dv ≤ (Real.pi / L) ^ 2) (n : ℕ) :
    ¬ IsUnstableMode J du dv (neumannWavenumber L n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [neumannWavenumber] using not_isUnstableMode_zero htr hdet du dv
  · rw [isUnstableMode_neumannWavenumber_iff hdu hdv htr hL]
    rintro ⟨-, -, hlt⟩
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpl : 0 < Real.pi / L := div_pos Real.pi_pos hL
    have : Real.pi / L ≤ n * Real.pi / L := by
      rw [mul_div_assoc]
      nlinarith
    have : (Real.pi / L) ^ 2 ≤ (n * Real.pi / L) ^ 2 := pow_le_pow_left₀ hpl.le this 2
    linarith

/-- Every long enough interval has a squared Neumann wavenumber inside a given nonempty open band
`(qlo, qhi)` with `0 < qhi`: there is `L₀ > 0` such that for all `L ≥ L₀` some `(n π / L)²` lies
in `(qlo, qhi)`. -/
theorem exists_neumann_mem_band {qlo qhi : ℝ} (hlt : qlo < qhi) (hpos : 0 < qhi) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∃ n : ℕ, qlo < (n * Real.pi / L) ^ 2 ∧
      (n * Real.pi / L) ^ 2 < qhi := by
  let a := Real.sqrt (max qlo 0)
  let b := Real.sqrt qhi
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hab : a < b := Real.sqrt_lt_sqrt (le_max_right qlo 0) (max_lt hlt hpos)
  have ha2 : a ^ 2 = max qlo 0 := Real.sq_sqrt (le_max_right qlo 0)
  have hb2 : b ^ 2 = qhi := Real.sq_sqrt hpos.le
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hpi := Real.pi_pos
  have hL0 : 0 < 2 * Real.pi / (b - a) := div_pos (by positivity) hgap
  refine ⟨2 * Real.pi / (b - a), hL0, ?_⟩
  intro L hLbound
  have hL : 0 < L := lt_of_lt_of_le hL0 hLbound
  let n := ⌊a * L / Real.pi⌋₊ + 1
  have hx : 0 ≤ a * L / Real.pi := div_nonneg (mul_nonneg ha hL.le) hpi.le
  have hnlo : a * L / Real.pi < (n : ℝ) := by
    simpa [n] using Nat.lt_floor_add_one (a * L / Real.pi)
  have hnhi : (n : ℝ) ≤ a * L / Real.pi + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le hx) (1 : ℝ)
  have hal : a * L < n * Real.pi := (div_lt_iff₀ hpi).mp hnlo
  have hnl : n * Real.pi ≤ a * L + Real.pi := by
    have h := (mul_le_mul_of_nonneg_right hnhi hpi.le)
    field_simp at h
    nlinarith only [h]
  have hroom : 2 * Real.pi ≤ (b - a) * L := by
    have h := (div_le_iff₀ hgap).mp hLbound
    nlinarith only [h]
  have hwlo : a < n * Real.pi / L := (lt_div_iff₀ hL).mpr hal
  have hwhi : n * Real.pi / L < b := by
    apply (div_lt_iff₀ hL).mpr
    nlinarith only [hnl, hroom, hpi]
  refine ⟨n, ?_, ?_⟩
  · have hmax := le_max_left qlo 0
    nlinarith only [hwlo, ha, ha2, hmax]
  · nlinarith only [hwlo, hwhi, ha, hb, hb2]

/-- **Large domains pattern.** Under Turing's criterion, every long enough interval `[0, L]` has
an unstable Neumann mode. -/
theorem exists_isUnstableMode_neumannWavenumber {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (_hdet : 0 < J.det)
    (h : 2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∃ n : ℕ, IsUnstableMode J du dv (neumannWavenumber L n) := by
  obtain ⟨hS, hsq⟩ := two_mul_sqrt_lt_iff.1 h
  have hΔ : 0 < bandDiscriminant J du dv := by
    unfold bandDiscriminant
    linarith
  have hr : 0 < Real.sqrt (bandDiscriminant J du dv) := Real.sqrt_pos.2 hΔ
  have hp : 0 < 2 * du * dv := by positivity
  have hlt : bandLower J du dv < bandUpper J du dv := by
    unfold bandLower bandUpper
    exact div_lt_div_of_pos_right (by linarith) hp
  have hpos : 0 < bandUpper J du dv := by
    unfold bandUpper
    exact div_pos (by linarith) hp
  obtain ⟨L₀, hL₀, hL⟩ := exists_neumann_mem_band hlt hpos
  refine ⟨L₀, hL₀, fun L hL₀L => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le hL₀ hL₀L
  obtain ⟨n, h1, h2⟩ := hL L hL₀L
  exact ⟨n, (isUnstableMode_neumannWavenumber_iff hdu hdv htr hLpos n).2 ⟨hΔ, h1, h2⟩⟩

/-! ### Schnakenberg kinetics -/

/-- Schnakenberg's reaction terms `(f, g) = (a - u + u² v, b - u² v)` as a map on
`x = (u, v) : Fin 2 → ℝ`, with source rates `a, b` (biologically `a, b > 0`). -/
def schnakenberg (a b : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a - x 0 + x 0 ^ 2 * x 1, b - x 0 ^ 2 * x 1]

/-- The homogeneous steady state `(u₀, v₀) = (a + b, b / (a + b)²)` of the Schnakenberg
kinetics (meaningful for `a + b ≠ 0`; at `a + b = 0` the division gives the junk `v₀ = 0`). -/
noncomputable def schnakenbergSteadyState (a b : ℝ) : Fin 2 → ℝ :=
  ![a + b, b / (a + b) ^ 2]

/-- The Jacobian of the Schnakenberg kinetics at its steady state,
`[[(b - a) / (a + b), (a + b)²], [-2 b / (a + b), -(a + b)²]]`. -/
noncomputable def schnakenbergJacobian (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(b - a) / (a + b), (a + b) ^ 2; -(2 * b) / (a + b), -(a + b) ^ 2]

/-- `(a + b, b / (a + b)²)` is a steady state of the Schnakenberg kinetics when `a + b ≠ 0`. -/
theorem schnakenberg_steadyState {a b : ℝ} (hab : a + b ≠ 0) :
    schnakenberg a b (schnakenbergSteadyState a b) = 0 := by
  funext i
  fin_cases i <;> simp [schnakenberg, schnakenbergSteadyState] <;> field_simp <;> ring

/-- The Jacobian matrix of the Schnakenberg kinetics at the steady state is
`schnakenbergJacobian a b`. -/
theorem jacobianMatrix_schnakenberg {a b : ℝ} (hab : a + b ≠ 0) :
    MetaMathlibExt.jacobianMatrix (schnakenberg a b) (schnakenbergSteadyState a b) =
      schnakenbergJacobian a b := by
  have h1 : HasDerivAt (fun t : ℝ => a + b + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add _
  have h2 : HasDerivAt (fun t : ℝ => b / (a + b) ^ 2 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [schnakenbergSteadyState, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      MetaMathlibExt.jacobianMatrix_apply, schnakenberg, Pi.add_apply, cons_val_zero,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, cons_val_one, cons_val_fin_one,
      ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      sub_add_cancel_left, schnakenbergJacobian, of_apply, cons_val']
  · rw [((h1.const_sub a).fun_add ((h1.fun_pow 2).mul_const (b / (a + b) ^ 2))).deriv]
    field_simp
    ring
  · rw [((h2.const_mul ((a + b) ^ 2)).const_add (-b)).deriv]
    ring
  · rw [((h1.fun_pow 2).mul_const (b / (a + b) ^ 2)).const_sub b |>.deriv]
    field_simp
    ring
  · rw [((h2.const_mul ((a + b) ^ 2)).const_sub b).deriv]
    ring

/-- `det J = (a + b)²` for the Schnakenberg Jacobian (`a + b ≠ 0`). -/
theorem det_schnakenbergJacobian {a b : ℝ} (hab : a + b ≠ 0) :
    (schnakenbergJacobian a b).det = (a + b) ^ 2 := by
  rw [schnakenbergJacobian, Matrix.det_fin_two_of]
  field_simp
  ring

/-- The Schnakenberg steady state is stable without diffusion iff `b - a < (a + b)³`
(for `0 < a + b`; then `0 < det J` automatically). -/
theorem trace_schnakenbergJacobian_neg_iff {a b : ℝ} (hab : 0 < a + b) :
    (schnakenbergJacobian a b).trace < 0 ↔ b - a < (a + b) ^ 3 := by
  simp only [schnakenbergJacobian, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [show (b - a) / (a + b) + -(a + b) ^ 2 = (b - a - (a + b) ^ 3) / (a + b) by
    field_simp; ring, div_lt_iff₀ hab, zero_mul, sub_neg]

/-- **Turing instability of the Schnakenberg kinetics** (Murray 2003, ch. 2). With
`d_u = 1`, `d_v = d > 0`, `0 < a + b` and `b - a < (a + b)³` (stable without diffusion), some
Fourier mode is unstable iff `2 √d (a + b)² < d (b - a) - (a + b)³`. -/
theorem schnakenberg_turing_iff {a b d : ℝ} (hab : 0 < a + b) (hstab : b - a < (a + b) ^ 3)
    (hd : 0 < d) :
    (∃ k, IsUnstableMode (schnakenbergJacobian a b) 1 d k) ↔
      2 * Real.sqrt d * (a + b) ^ 2 < d * (b - a) - (a + b) ^ 3 := by
  have hdet : 0 < (schnakenbergJacobian a b).det := by
    rw [det_schnakenbergJacobian hab.ne']
    positivity
  rw [exists_isUnstableMode_iff one_pos hd ((trace_schnakenbergJacobian_neg_iff hab).2 hstab)
    hdet, det_schnakenbergJacobian hab.ne', one_mul, Real.sqrt_mul hd.le, Real.sqrt_sq hab.le]
  simp only [schnakenbergJacobian, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [← sub_pos, ← sub_pos (a := d * (b - a) - (a + b) ^ 3)]
  have : d * (b - a) - (a + b) ^ 3 - 2 * Real.sqrt d * (a + b) ^ 2 =
      (a + b) * (d * ((b - a) / (a + b)) + 1 * -(a + b) ^ 2 - 2 * (Real.sqrt d * (a + b))) := by
    field_simp
    ring
  rw [this, mul_pos_iff_of_pos_left hab]

/-! ### Gierer–Meinhardt kinetics -/

/-- Gierer–Meinhardt activator-inhibitor kinetics in Murray's nondimensional form
`(f, g) = (a - b u + u² / v, u² - v)` on `x = (u, v)` (biologically `a, b > 0` and `u, v > 0`;
at `v = 0` the division gives the junk `u² / 0 = 0`). -/
noncomputable def giererMeinhardt (a b : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a - b * x 0 + x 0 ^ 2 / x 1, x 0 ^ 2 - x 1]

/-- The homogeneous steady state `(u₀, v₀) = ((a + 1) / b, ((a + 1) / b)²)` of the
Gierer–Meinhardt kinetics (meaningful for `b ≠ 0`, `a + 1 ≠ 0`). -/
noncomputable def giererMeinhardtSteadyState (a b : ℝ) : Fin 2 → ℝ :=
  ![(a + 1) / b, ((a + 1) / b) ^ 2]

/-- The Jacobian of the Gierer–Meinhardt kinetics at its steady state,
`[[b (1 - a) / (1 + a), -(b / (a + 1))²], [2 (a + 1) / b, -1]]`. -/
noncomputable def giererMeinhardtJacobian (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b * (1 - a) / (1 + a), -(b / (a + 1)) ^ 2; 2 * (a + 1) / b, -1]

/-- `((a + 1) / b, ((a + 1) / b)²)` is a steady state of the Gierer–Meinhardt kinetics when
`a + 1 ≠ 0` and `b ≠ 0`. -/
theorem giererMeinhardt_steadyState {a b : ℝ} (ha : a + 1 ≠ 0) (hb : b ≠ 0) :
    giererMeinhardt a b (giererMeinhardtSteadyState a b) = 0 := by
  funext i
  fin_cases i
  · simp only [giererMeinhardt, giererMeinhardtSteadyState, Fin.zero_eta, Fin.isValue,
      cons_val_zero, cons_val_one, cons_val_fin_one, Pi.zero_apply]
    field_simp
    ring
  · simp [giererMeinhardt, giererMeinhardtSteadyState]

/-- The Jacobian matrix of the Gierer–Meinhardt kinetics at the steady state is
`giererMeinhardtJacobian a b`. -/
theorem jacobianMatrix_giererMeinhardt {a b : ℝ} (ha : a + 1 ≠ 0) (hb : b ≠ 0) :
    MetaMathlibExt.jacobianMatrix (giererMeinhardt a b) (giererMeinhardtSteadyState a b) =
      giererMeinhardtJacobian a b := by
  have hc : (a + 1) / b ≠ 0 := div_ne_zero ha hb
  have ha' : 1 + a ≠ 0 := by rwa [add_comm]
  have h1 : HasDerivAt (fun t : ℝ => (a + 1) / b + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add _
  have h2 : HasDerivAt (fun t : ℝ => ((a + 1) / b) ^ 2 + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [giererMeinhardtSteadyState, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      MetaMathlibExt.jacobianMatrix_apply, giererMeinhardt, Pi.add_apply, cons_val_zero,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, cons_val_one, cons_val_fin_one,
      ne_eq, one_ne_zero, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      sub_add_cancel_left, deriv_const_add', deriv_sub_const_fun,
      deriv_neg'', giererMeinhardtJacobian, of_apply, cons_val']
  · rw [((h1.const_mul b).const_sub a).fun_add ((h1.fun_pow 2).div_const _) |>.deriv]
    norm_num
    field_simp
    ring
  · rw [((hasDerivAt_const (0 : ℝ) (((a + 1) / b) ^ 2)).fun_div h2 (by simpa using hc)).deriv]
    field_simp
    ring
  · rw [(h1.fun_pow 2).deriv]
    norm_num
    field_simp

/-- `det J = b` for the Gierer–Meinhardt Jacobian (`a + 1 ≠ 0`, `b ≠ 0`). -/
theorem det_giererMeinhardtJacobian {a b : ℝ} (ha : a + 1 ≠ 0) (hb : b ≠ 0) :
    (giererMeinhardtJacobian a b).det = b := by
  have ha' : 1 + a ≠ 0 := by rwa [add_comm]
  rw [giererMeinhardtJacobian, Matrix.det_fin_two_of]
  field_simp
  ring

/-- The Gierer–Meinhardt steady state is stable without diffusion iff `b (1 - a) < 1 + a`
(for `0 < a + 1`; then `0 < det J = b` for `0 < b`). -/
theorem trace_giererMeinhardtJacobian_neg_iff {a b : ℝ} (ha : 0 < a + 1) :
    (giererMeinhardtJacobian a b).trace < 0 ↔ b * (1 - a) < 1 + a := by
  have ha' : 0 < 1 + a := by linarith
  simp only [giererMeinhardtJacobian, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [show b * (1 - a) / (1 + a) + -1 = (b * (1 - a) - (1 + a)) / (1 + a) by
    field_simp; ring, div_lt_iff₀ ha', zero_mul, sub_neg]

/-- **Turing instability of the Gierer–Meinhardt kinetics.** With `d_u = 1`, `d_v = d > 0`,
`0 < a + 1`, `0 < b` and `b (1 - a) < 1 + a` (stable without diffusion), some Fourier mode is
unstable iff `2 √(d b) < d b (1 - a) / (1 + a) - 1`. -/
theorem giererMeinhardt_turing_iff {a b d : ℝ} (ha : 0 < a + 1) (hb : 0 < b)
    (hstab : b * (1 - a) < 1 + a) (hd : 0 < d) :
    (∃ k, IsUnstableMode (giererMeinhardtJacobian a b) 1 d k) ↔
      2 * Real.sqrt (d * b) < d * (b * (1 - a) / (1 + a)) - 1 := by
  have hdet : 0 < (giererMeinhardtJacobian a b).det := by
    rwa [det_giererMeinhardtJacobian ha.ne' hb.ne']
  rw [exists_isUnstableMode_iff one_pos hd ((trace_giererMeinhardtJacobian_neg_iff ha).2 hstab)
    hdet, det_giererMeinhardtJacobian ha.ne' hb.ne', one_mul]
  simp only [giererMeinhardtJacobian, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor <;> intro h <;> linarith

end MathlibExt.Biology.Dynamics.TuringPatterns
