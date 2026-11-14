/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Quantum.FiniteState
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-dimensional model systems with explicit domains

Particle in a box, low-lying harmonic-oscillator states, the ladder
commutator as a pointwise identity for Schwartz functions, box moments, and
a free-electron polyene absorption model.

## i. Overview

This module formalizes the ATLAS CH37 one-dimensional-model-systems pilot:
the particle in a box (eigenfunctions, eigen-equation, Dirichlet boundary
conditions, orthonormality), the harmonic oscillator (low-lying eigenstates
and eigen-equations in `ħ = m = ω = 1` units), the ladder commutator
`a a† - a† a = 1` as a pointwise identity of differential expressions for
Schwartz functions, box position moments, and a free-electron estimate of
polyene absorption wavelengths.

Conventions used consistently throughout: box functions are real-valued
(`ℝ → ℝ`) with symbolic `L > 0`, `m > 0`, `ħ > 0`; oscillator and ladder
functions are complex-valued (`ℝ → ℂ`); the ladder algebra and the
oscillator eigen-equations of this module use `ħ = m = ω = 1` units (stated
explicitly at each result; the general-constants ladder identity is NOT
claimed). Planck's constant is DEFINED as `h = 2 * π * ħ` (`planckH`); no
numeric SI value is asserted for any constant.

Model boundary: MOD covers the model potentials (box walls, harmonic
potential, free-electron polyene); MC covers eigenfunction verification,
box orthonormality, and full `{0,1,2}` oscillator orthonormality. No claim
of self-adjointness or completeness is made without an explicit domain and
proof (see the deferrals below).

## ii. Key results

* `box_eigen_equation`: pointwise eigen-equation for the box states.
* `box_orthonormality`: orthonormality of the box states on `(0, L)`.
* `box_mem_BoxC2Dirichlet`: box states lie in `BoxC2Dirichlet L` (real `C²`
  functions vanishing at `0` and `L`; not the Sobolev domain `H² ∩ H¹₀`).
* `osc_eigen_0/1/2`: oscillator eigen-equations for `v ∈ {0, 1, 2}`.
* `ladder_commutator_pointwise_schwartz`: `annFun (creFun f) - creFun (annFun f) = f`
  pointwise for Schwartz `f`, a formal identity of the differential expressions.
* `box_moment_x`, `box_moment_x2`: `⟨x⟩` and `⟨x^2⟩` for box states.
* `polyene_wavelength_closed_form`: closed form of the model wavelength.

## iii. Table of contents

* Section A: particle in a box.
* Section B: harmonic oscillator (low-lying states, Physlib reuse noted).
* Section C: the pointwise ladder identity; box moments.
* Section D: free-electron polyene model.
* Section E (in this doc only): explicit deferrals.

## iv. References

* MIT OCW 5.61 Physical Chemistry, Fall 2017, Lectures 8 (harmonic
  oscillator) and related particle-in-a-box material.
* Pinned Physlib `Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/`,
  for Physlib's `HarmonicOscillator` structure and its physical constants
  (cited in prose; none of these statements is restated here): the
  general-`v` eigen-equation is
  `QuantumMechanics.OneDimension.HarmonicOscillator.schrodingerOperator_eigenfunction`
  (`TISE.lean`); orthonormality of all eigenfunctions is
  `QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_orthonormal`
  (`Eigenfunction.lean`); completeness is `eigenfunction_completeness`
  (`Completeness.lean`), proved there with Plancherel's theorem taken as a
  hypothesis.
* Pinned Physlib `Physlib/QuantumMechanics/HarmonicOscillator/LadderOperators.lean`:
  the ladder operators of the `d`-dimensional oscillator as continuous linear
  maps on Schwartz space, with the operator commutator
  `QuantumMechanics.HarmonicOscillator.lowering_commutation_raising`. The
  pointwise identity of this module is not that operator statement.
* Pinned Physlib `Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean`
  (domain-embedding operator pattern).
* MF10 `PhyslibExt.Quantum.FiniteState` (ATLAS main): `OperatorWithDomain`
  pattern reused for the ladder operators (record fields verified against
  merged main as `domain`/`op`, non-generic over `ℝ → ℂ`).

## A. Particle in a box

`boxFunction n L` is the `n`-th box eigenfunction and `boxEnergy n L m ħ`
is `n^2 h^2 / (8 m L^2)` with `h = 2πħ`. We prove the equivalent form
`n^2 π^2 ħ^2 / (2 m L^2)`, the pointwise eigen-equation (two `deriv`s),
Dirichlet boundary values, orthonormality on `(0, L)` by product-to-sum
plus cosine interval integrals, and membership in the smooth Dirichlet
carrier `BoxC2Dirichlet L`.

## B. Harmonic oscillator

The general-`v` eigen-equation `H ψᵥ = Eᵥ ψᵥ` with
`E_v = (v + 1/2) * ħ * ω` (general symbols) is Physlib's proved
`schrodingerOperator_eigenfunction`, cited in prose (see section iv).
This module proves the `ħ = m = ω = 1` instance
`-(1/2) * ψᵥ'' x + (1/2) * x^2 * ψᵥ x = (v + 1/2) * ψᵥ x` for the explicit
normalized states `v ∈ {0, 1, 2}` (`oscFun0/1/2`, built from explicit
polynomial factors `1`, `x`, `2x^2 - 1` with rescaled prefactors (the
physicist-Hermite polynomials `1`, `2x`, `4x^2 - 2` up to normalization;
no competing Hermite definition is introduced, and Mathlib's probabilist
`Polynomial.hermite` is not used since the physicist form is needed here),
plus the full `{0,1,2}^2` orthonormality integrals from explicit Gaussian
moments.

## C. Ladder operators and box moments

Annihilation/creation functions `annFun`/`creFun` in `ħ = m = ω = 1`
units with the sign convention `a f = (x·f + f')/√2`,
`a† f = (x·f - f')/√2`; the pointwise identity
`annFun (creFun f) x - creFun (annFun f) x = f x` for every `f` in the
Schwartz carrier (`SchwartzCarrier`, Mathlib `SchwartzMap`); and the box
moments `⟨x⟩ = L/2`, `⟨x^2⟩ = L^2 (1/3 - 1/(2n^2π^2))` by `sin^2`
interval integrals. The identity is a formal one between differential
expressions: it composes the total functions `annFun` and `creFun`, not the
records `annihilation` and `creation`. Closure of the Schwartz carrier under
`annFun`/`creFun` is not proved, so those records, whose domain is the
Schwartz carrier, cannot be composed, and no operator commutator on Schwartz
space is claimed here (Physlib's `lowering_commutation_raising` is such a
statement; see section iv).

## D. Polyene model

MODEL (free-electron + box): for `k` double bonds, `N = 2k`
π-electrons, `L = (2k+1)a`, HOMO `n = k`, LUMO `n = k+1`, gap from
`boxEnergy`, wavelength `h c / ΔE`. The closed form
`8 m c L^2 / (h (2k+1))` is proved by algebra. This is a model estimate,
not a measurement or a theorem about real polyenes; `a`, `L`, `c` are
model inputs.

## E. Explicit deferrals (visible; never silent)

* Completeness of the box eigenfunctions in `L^2(0, L)` and
  self-adjointness of the box Hamiltonian on `H^2 ∩ H^1_0`: DEFERRED
  (allowed by the contract). Nothing in this module proves or assumes
  either statement. Sobolev regularity is NOT developed here, and the
  Sobolev domain `H²(0, L) ∩ H¹₀(0, L)` is not modeled: `BoxC2Dirichlet` is
  only a carrier of smooth real functions.
* General-`v` oscillator eigen-equation: Physlib's proved result, cited
  in prose only (see section iv).
* General-`v` oscillator orthonormality: Physlib's proved
  `eigenfunction_orthonormal`, for Physlib's `HarmonicOscillator` and its
  constants, cited in prose only (see section iv); not restated here.
* Oscillator orthonormality for `(v, w) ∈ {0,1,2}^2`: PROVED
  (`osc_orthonormality_00/01/10/02/20/11/12/21/22`) by explicit Gaussian
  moments: odd vanishing of `∫ x·e^(-x^2)` and `∫ x^3·e^(-x^2)` by
  whole-line negation symmetry, and even moments `∫ x^2·e^(-x^2)` and
  `∫ x^4·e^(-x^2)` by integration by parts from the base integral.
  General-`v` orthonormality (beyond `{0,1,2}`) is not restated here
  (see the Physlib citation above).
-/

@[expose] public section

namespace Chemistry.Quantum.OneDimensionalModels

/-! ## Section A: particle in a box. -/

/-- `n`-th particle-in-a-box eigenfunction (real-valued). -/
noncomputable def boxFunction (n : ℕ) (L : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L)

/-- Box energy `n^2 h^2 / (8 m L^2)` with `h = 2πħ`. -/
noncomputable def boxEnergy (n : ℕ) (L m ħ : ℝ) : ℝ :=
  (↑n ^ 2 * (2 * Real.pi * ħ) ^ 2) / (8 * m * L ^ 2)

/-- Planck's constant, DEFINED as `h = 2 * π * ħ`. -/
noncomputable def planckH (ħ : ℝ) : ℝ := 2 * Real.pi * ħ

/-- Equivalent form `boxEnergy n L m ħ = n^2 π^2 ħ^2 / (2 m L^2)`,
by ring-field arithmetic. -/
lemma boxEnergy_equiv (n : ℕ) (L m ħ : ℝ) :
    boxEnergy n L m ħ = ↑n ^ 2 * Real.pi ^ 2 * ħ ^ 2 / (2 * m * L ^ 2) := by
  unfold boxEnergy
  ring

/-- Derivative of the affine inner function `c * x / L`
(Mathlib `HasDerivAt` API: `hasDerivAt_const`, `hasDerivAt_id`,
`HasDerivAt.mul`, `HasDerivAt.div_const`). -/
private lemma hasDerivAt_affine (c L : ℝ) (x : ℝ) :
    HasDerivAt (fun x => c * x / L) (c / L) x := by
  have h0 := ((hasDerivAt_const x c).mul (hasDerivAt_id x)).div_const L
  convert h0 using 1
  all_goals try funext y
  all_goals try simp only [Pi.mul_apply, id_eq, zero_mul, mul_zero, mul_one, one_mul,
    zero_add, add_zero, sub_zero, zero_sub, sub_self, neg_zero]
  all_goals try field_simp
  all_goals try ring

/-- Derivative of `sin` of the affine inner function
(Mathlib `HasDerivAt.sin`). -/
private lemma hasDerivAt_sin_affine (c L : ℝ) (x : ℝ) :
    HasDerivAt (fun x => Real.sin (c * x / L))
      (Real.cos (c * x / L) * (c / L)) x := by
  have h0 := (hasDerivAt_affine c L x).sin
  convert h0 using 1
  all_goals try funext y
  all_goals try simp only [Pi.mul_apply, id_eq]
  all_goals try field_simp
  all_goals try ring

/-- Derivative of `cos` of the affine inner function
(Mathlib `HasDerivAt.cos`). -/
private lemma hasDerivAt_cos_affine (c L : ℝ) (x : ℝ) :
    HasDerivAt (fun x => Real.cos (c * x / L))
      (-Real.sin (c * x / L) * (c / L)) x := by
  have h0 := (hasDerivAt_affine c L x).cos
  convert h0 using 1
  all_goals try funext y
  all_goals try simp only [Pi.mul_apply, id_eq]
  all_goals try field_simp
  all_goals try ring

/-- First derivative of the box function (pointwise). -/
private lemma box_deriv_first (n : ℕ) (L : ℝ) (x : ℝ) :
    deriv (boxFunction n L) x
      = Real.sqrt (2 / L)
        * ((↑n * Real.pi / L) * Real.cos (↑n * Real.pi * x / L)) := by
  have h0 : HasDerivAt
      (fun x => Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L))
      (Real.sqrt (2 / L)
        * (Real.cos (↑n * Real.pi * x / L) * (↑n * Real.pi / L))) x := by
    have h1 := ((hasDerivAt_affine (↑n * Real.pi) L x).sin.const_mul
      (Real.sqrt (2 / L)))
    convert h1 using 1
    all_goals try funext y
    all_goals try simp only [Pi.mul_apply, id_eq]
    all_goals try field_simp
    all_goals try ring
  have h := h0.deriv
  rw [show boxFunction n L
    = (fun x => Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L)) from rfl]
  exact h.trans (by ring)

/-- Second derivative of the box function (pointwise). -/
private lemma box_deriv_second (n : ℕ) (L : ℝ) (x : ℝ) :
    deriv (deriv (boxFunction n L)) x
      = -(Real.sqrt (2 / L)
        * ((↑n * Real.pi / L) ^ 2 * Real.sin (↑n * Real.pi * x / L))) := by
  have hfirst : deriv (boxFunction n L)
      = fun x => Real.sqrt (2 / L)
        * ((↑n * Real.pi / L) * Real.cos (↑n * Real.pi * x / L)) := by
    funext y
    exact box_deriv_first n L y
  rw [hfirst]
  have h0 : HasDerivAt (fun x => Real.sqrt (2 / L)
      * ((↑n * Real.pi / L) * Real.cos (↑n * Real.pi * x / L)))
    (Real.sqrt (2 / L)
      * ((↑n * Real.pi / L)
        * (-Real.sin (↑n * Real.pi * x / L) * (↑n * Real.pi / L)))) x := by
    have h1 := (((hasDerivAt_affine (↑n * Real.pi) L x).cos.const_mul
      (↑n * Real.pi / L)).const_mul (Real.sqrt (2 / L)))
    convert h1 using 1
    all_goals try funext y
    all_goals try simp only [Pi.mul_apply, id_eq]
    all_goals try field_simp
    all_goals try ring
  have h := h0.deriv
  exact h.trans (by ring)

/-- Pointwise eigen-equation for the box states: with `H = -(ħ^2/2m) d^2/dx^2`,
`H ψ_n = E_n ψ_n` (uses `deriv` twice; Mathlib `HasDerivAt.deriv`). -/
lemma box_eigen_equation (n : ℕ) (L m ħ x : ℝ) (hn : 1 ≤ n) (hL : 0 < L)
    (hm : 0 < m) :
    -(ħ ^ 2 / (2 * m)) * (deriv (deriv (boxFunction n L)) x)
      = boxEnergy n L m ħ * boxFunction n L x := by
  rw [box_deriv_second n L x]
  have hpt : boxFunction n L x
      = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L) := rfl
  rw [hpt]
  unfold boxEnergy
  ring

/-- Dirichlet boundary at `0` (uses `Real.sin` of `0`). -/
lemma box_dirichlet_zero (n : ℕ) (L : ℝ) (hn : 1 ≤ n) (hL : 0 < L) :
    boxFunction n L 0 = 0 := by
  have hpt : boxFunction n L 0
      = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * 0 / L) := rfl
  rw [hpt]
  have harg : ↑n * Real.pi * 0 / L = 0 := by ring
  rw [harg, Real.sin_zero, mul_zero]

/-- Dirichlet boundary at `L` (uses `Real.sin_nat_mul_pi`). -/
lemma box_dirichlet_right (n : ℕ) (L : ℝ) (hn : 1 ≤ n) (hL : 0 < L) :
    boxFunction n L L = 0 := by
  have hpt : boxFunction n L L
      = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * L / L) := rfl
  rw [hpt]
  have hL' : L ≠ 0 := ne_of_gt hL
  have harg : ↑n * Real.pi * L / L = ↑n * Real.pi := by
    field_simp
    try ring
  rw [harg, Real.sin_nat_mul_pi n, mul_zero]

/-- Smooth Dirichlet carrier for the box states: real-valued `C²` functions on `ℝ` vanishing
at `0` and `L`. It is not the Sobolev domain `H²(0, L) ∩ H¹₀(0, L)` of the box Hamiltonian,
whose elements are complex-valued `L²` classes with weak derivatives, and it is not a complex
vector space; no Hamiltonian domain is claimed. -/
def BoxC2Dirichlet (L : ℝ) : Set (ℝ → ℝ) :=
  {f | ContDiff ℝ 2 f ∧ f 0 = 0 ∧ f L = 0}

/-- The affine inner function is `C^2` (Mathlib `contDiff_id`,
`ContDiff.const_mul`). -/
private lemma contDiff_inner (c L : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => c * x / L) := by
  have heq : (fun x : ℝ => (c / L) * x) = (fun x : ℝ => c * x / L) := by
    funext x
    ring
  have h2 : ContDiff ℝ 2 (id : ℝ → ℝ) := contDiff_id
  simpa only [id_eq, smul_eq_mul, heq] using h2.const_smul (c / L)

/-- The box function is `C^2` (Mathlib `Real.contDiff_sin`,
`ContDiff.comp`, `ContDiff.const_mul`). -/
private lemma contDiff_box (n : ℕ) (L : ℝ) :
    ContDiff ℝ 2 (boxFunction n L) := by
  have hsin : ContDiff ℝ 2
      (fun x : ℝ => Real.sin (↑n * Real.pi * x / L)) :=
    Real.contDiff_sin.comp (contDiff_inner (↑n * Real.pi) L)
  have hfin : ContDiff ℝ 2 (fun x : ℝ =>
      Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L)) := by
    simpa only [smul_eq_mul] using hsin.const_smul (Real.sqrt (2 / L))
  exact hfin

/-- Box states lie in the smooth Dirichlet carrier `BoxC2Dirichlet L`. -/
lemma box_mem_BoxC2Dirichlet (n : ℕ) (L : ℝ) (hn : 1 ≤ n) (hL : 0 < L) :
    boxFunction n L ∈ BoxC2Dirichlet L := by
  show ContDiff ℝ 2 (boxFunction n L)
    ∧ boxFunction n L 0 = 0 ∧ boxFunction n L L = 0
  exact ⟨contDiff_box n L, box_dirichlet_zero n L hn hL,
    box_dirichlet_right n L hn hL⟩

/-- The affine inner function is continuous (Mathlib `continuous_const`,
`continuous_id`, `Continuous.mul`, `Continuous.div_const`). -/
private lemma continuous_inner (c L : ℝ) :
    Continuous (fun x : ℝ => c * x / L) := by
  fun_prop

/-- Cosine interval integral at positive integer frequency: for `m ≥ 1`,
`∫ x in 0..L, cos (m * π * x / L) = 0`, by the fundamental theorem of
calculus (Mathlib `intervalIntegral.integral_eq_sub_of_hasDerivAt`) with
antiderivative `(L / (m * π)) * sin (m * π * x / L)`. -/
lemma cos_integral_pos (m : ℕ) (L : ℝ) (hm : 1 ≤ m) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, Real.cos (↑m * Real.pi * x / L) = 0 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hF : ∀ x : ℝ, HasDerivAt
      (fun x => (L / (↑m * Real.pi)) * Real.sin (↑m * Real.pi * x / L))
      (Real.cos (↑m * Real.pi * x / L)) x := by
    intro x
    have hm0 : 0 < m := by omega
    have hm' : (↑m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm0
    have hmp : (↑m * Real.pi) ≠ 0 := mul_ne_zero hm' Real.pi_ne_zero
    have h0 := (hasDerivAt_sin_affine (↑m * Real.pi) L x).const_mul
      (L / (↑m * Real.pi))
    convert h0 using 1
    all_goals try funext y
    all_goals try simp only [Pi.mul_apply, id_eq]
    all_goals try field_simp
    all_goals try ring
  have hint : IntervalIntegrable
      (fun x => Real.cos (↑m * Real.pi * x / L)) MeasureTheory.volume 0 L := by
    have hc : Continuous (fun x => Real.cos (↑m * Real.pi * x / L)) := by
      fun_prop
    exact hc.intervalIntegrable 0 L
  have hFTC : (∫ x in (0:ℝ)..L, Real.cos (↑m * Real.pi * x / L))
      = (L / (↑m * Real.pi)) * Real.sin (↑m * Real.pi * L / L)
        - (L / (↑m * Real.pi)) * Real.sin (↑m * Real.pi * 0 / L) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint
  have hargL : ↑m * Real.pi * L / L = ↑m * Real.pi := by
    field_simp
    try ring
  have harg0 : ↑m * Real.pi * 0 / L = 0 := by ring
  rw [hFTC, hargL, harg0, Real.sin_nat_mul_pi m, Real.sin_zero, mul_zero,
    sub_zero]

/-- Diagonal orthonormality: `∫ x in 0..L, boxFunction n * boxFunction n = 1`,
via `sin^2 = (1 - cos 2θ)/2` (Mathlib `Real.cos_two_mul`,
`Real.sin_sq_add_cos_sq`) and `cos_integral_pos`. -/
lemma box_orthonormality_diag (n : ℕ) (L : ℝ) (hn : 1 ≤ n) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, boxFunction n L x * boxFunction n L x = 1 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have h2L : (0:ℝ) ≤ 2 / L := div_nonneg (by norm_num) (le_of_lt hL)
  have hA2 : Real.sqrt (2 / L) ^ 2 = 2 / L := Real.sq_sqrt h2L
  have hpt : ∀ x : ℝ, boxFunction n L x * boxFunction n L x
      = (2 / L) * (Real.sin (↑n * Real.pi * x / L)) ^ 2 := by
    intro x
    have hraw : boxFunction n L x * boxFunction n L x
        = (Real.sqrt (2 / L) ^ 2)
          * ((Real.sin (↑n * Real.pi * x / L)) ^ 2) := by
      have hpt0 : boxFunction n L x
          = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L) := rfl
      rw [hpt0]
      ring
    rw [hraw, hA2]
  have hsin2 : ∀ x : ℝ, (Real.sin (↑n * Real.pi * x / L)) ^ 2
      = (1 - Real.cos (2 * (↑n * Real.pi * x / L))) / 2 := by
    intro x
    have h1 := Real.cos_two_mul (↑n * Real.pi * x / L)
    have h2 := Real.sin_sq_add_cos_sq (↑n * Real.pi * x / L)
    linarith
  have hfun : (fun x : ℝ => boxFunction n L x * boxFunction n L x)
      = (fun x : ℝ => (1 / L)
        - (1 / L) * Real.cos (2 * (↑n * Real.pi * x / L))) := by
    funext x
    rw [hpt x, hsin2 x]
    ring
  rw [hfun]
  have hC : IntervalIntegrable (fun _ : ℝ => (1:ℝ) / L)
      MeasureTheory.volume 0 L :=
    continuous_const.intervalIntegrable 0 L
  have hK : IntervalIntegrable
      (fun x : ℝ => (1 / L) * Real.cos (2 * (↑n * Real.pi * x / L)))
      MeasureTheory.volume 0 L := by
    have hinner : Continuous (fun x : ℝ => 2 * (↑n * Real.pi * x / L)) :=
      (continuous_inner (↑n * Real.pi) L).const_mul 2
    exact ((Real.continuous_cos.comp hinner).const_mul _).intervalIntegrable 0 L
  have hsub : (∫ x in (0:ℝ)..L, (1 / L)
        - (1 / L) * Real.cos (2 * (↑n * Real.pi * x / L)))
      = (∫ x in (0:ℝ)..L, (1:ℝ) / L)
        - ∫ x in (0:ℝ)..L, (1 / L)
          * Real.cos (2 * (↑n * Real.pi * x / L)) :=
    intervalIntegral.integral_sub hC hK
  have eConst : (∫ x in (0:ℝ)..L, (1:ℝ) / L) = 1 := by
    have h : (∫ x in (0:ℝ)..L, (1:ℝ) / L) = (L - 0) • ((1:ℝ) / L) :=
      intervalIntegral.integral_const _
    rw [h]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    try ring
  have eCos : (∫ x in (0:ℝ)..L, (1 / L)
      * Real.cos (2 * (↑n * Real.pi * x / L))) = 0 := by
    have hfun2 : (fun x : ℝ => (1 / L)
          * Real.cos (2 * (↑n * Real.pi * x / L)))
        = (fun x : ℝ => (1 / L)
          * Real.cos (↑(2 * n) * Real.pi * x / L)) := by
      funext x
      have harg : 2 * (↑n * Real.pi * x / L)
          = ↑(2 * n) * Real.pi * x / L := by
        push_cast
        ring
      rw [harg]
    rw [hfun2]
    have hcm : (∫ x in (0:ℝ)..L, (1 / L)
          * Real.cos (↑(2 * n) * Real.pi * x / L))
        = (1 / L) * ∫ x in (0:ℝ)..L,
          Real.cos (↑(2 * n) * Real.pi * x / L) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm, cos_integral_pos (2 * n) L (by omega) hL, mul_zero]
  rw [hsub, eConst, eCos, sub_zero]

/-- Off-diagonal case with `n < k`, via product-to-sum
(`sin a * sin b = (cos (a-b) - cos (a+b))/2` from Mathlib `Real.cos_sub`
and `Real.cos_add`) plus `cos_integral_pos` at the positive frequencies
`k - n` and `n + k`. -/
private lemma box_orthonormality_offdiag_lt (n k : ℕ) (L : ℝ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hlt : n < k) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, boxFunction n L x * boxFunction k L x = 0 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have h2L : (0:ℝ) ≤ 2 / L := div_nonneg (by norm_num) (le_of_lt hL)
  have hA2 : Real.sqrt (2 / L) ^ 2 = 2 / L := Real.sq_sqrt h2L
  have hA2' : Real.sqrt (2 / L) * Real.sqrt (2 / L) = 2 / L := by
    rw [← pow_two, hA2]
  have hpt : ∀ x : ℝ, boxFunction n L x * boxFunction k L x
      = (1 / L) * (Real.cos (((↑n - ↑k)) * Real.pi * x / L)
        - Real.cos (((↑n + ↑k)) * Real.pi * x / L)) := by
    intro x
    have h1 := Real.cos_sub (↑n * Real.pi * x / L) (↑k * Real.pi * x / L)
    have h2 := Real.cos_add (↑n * Real.pi * x / L) (↑k * Real.pi * x / L)
    have hdiff : Real.cos ((↑n * Real.pi * x / L) - (↑k * Real.pi * x / L))
          - Real.cos ((↑n * Real.pi * x / L) + (↑k * Real.pi * x / L))
        = 2 * (Real.sin (↑n * Real.pi * x / L)
          * Real.sin (↑k * Real.pi * x / L)) := by
      linear_combination h1 - h2
    have hprod : Real.sin (↑n * Real.pi * x / L)
          * Real.sin (↑k * Real.pi * x / L)
        = (Real.cos ((↑n * Real.pi * x / L) - (↑k * Real.pi * x / L))
          - Real.cos ((↑n * Real.pi * x / L)
            + (↑k * Real.pi * x / L))) / 2 := by
      linear_combination -hdiff / 2
    have hpt0 : boxFunction n L x
        = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L) := rfl
    have hpt1 : boxFunction k L x
        = Real.sqrt (2 / L) * Real.sin (↑k * Real.pi * x / L) := rfl
    have e1 : ((↑n - ↑k)) * Real.pi * x / L
        = (↑n * Real.pi * x / L) - (↑k * Real.pi * x / L) := by ring
    have e2 : ((↑n + ↑k)) * Real.pi * x / L
        = (↑n * Real.pi * x / L) + (↑k * Real.pi * x / L) := by ring
    have hmid : Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L)
          * (Real.sqrt (2 / L) * Real.sin (↑k * Real.pi * x / L))
        = (Real.sqrt (2 / L) * Real.sqrt (2 / L))
          * (Real.sin (↑n * Real.pi * x / L)
            * Real.sin (↑k * Real.pi * x / L)) := by ring
    rw [hpt0, hpt1, e1, e2, hmid, hA2', hprod]
    ring
  have hle : n ≤ k := le_of_lt hlt
  have hcast : ((k - n : ℕ) : ℝ) = ↑k - ↑n := Nat.cast_sub hle
  have hd : 1 ≤ k - n := by omega
  have hfun : (fun x : ℝ => boxFunction n L x * boxFunction k L x)
      = (fun x : ℝ => (1 / L)
        * (Real.cos (↑(k - n) * Real.pi * x / L)
          - Real.cos (↑(n + k) * Real.pi * x / L))) := by
    funext x
    rw [hpt x]
    have eNeg : ((↑n - ↑k)) * Real.pi * x / L
        = -(↑(k - n) * Real.pi * x / L) := by
      rw [hcast]
      ring
    have eSum : ((↑n + ↑k)) * Real.pi * x / L
        = ((n + k : ℕ) : ℝ) * Real.pi * x / L := by
      rw [Nat.cast_add]
    rw [eNeg, Real.cos_neg, eSum]
  rw [hfun]
  have hK1 : IntervalIntegrable
      (fun x : ℝ => (1 / L) * Real.cos (↑(k - n) * Real.pi * x / L))
      MeasureTheory.volume 0 L := by
    have hinner : Continuous
        (fun x : ℝ => ↑(k - n) * Real.pi * x / L) :=
      continuous_inner (↑(k - n) * Real.pi) L
    exact ((Real.continuous_cos.comp hinner).const_mul _).intervalIntegrable 0 L
  have hK2 : IntervalIntegrable
      (fun x : ℝ => (1 / L) * Real.cos (↑(n + k) * Real.pi * x / L))
      MeasureTheory.volume 0 L := by
    have hinner : Continuous
        (fun x : ℝ => ↑(n + k) * Real.pi * x / L) :=
      continuous_inner (↑(n + k) * Real.pi) L
    exact ((Real.continuous_cos.comp hinner).const_mul _).intervalIntegrable 0 L
  have hsub : (∫ x in (0:ℝ)..L, (1 / L)
        * (Real.cos (↑(k - n) * Real.pi * x / L)
          - Real.cos (↑(n + k) * Real.pi * x / L)))
      = (∫ x in (0:ℝ)..L, (1 / L)
          * Real.cos (↑(k - n) * Real.pi * x / L))
        - ∫ x in (0:ℝ)..L, (1 / L)
          * Real.cos (↑(n + k) * Real.pi * x / L) := by
    have hfunsub : (fun x : ℝ => (1 / L)
          * (Real.cos (↑(k - n) * Real.pi * x / L)
            - Real.cos (↑(n + k) * Real.pi * x / L)))
        = (fun x : ℝ => (1 / L) * Real.cos (↑(k - n) * Real.pi * x / L)
          - (1 / L) * Real.cos (↑(n + k) * Real.pi * x / L)) := by
      funext x
      ring
    rw [hfunsub]
    exact intervalIntegral.integral_sub hK1 hK2
  have e1 : (∫ x in (0:ℝ)..L, (1 / L)
      * Real.cos (↑(k - n) * Real.pi * x / L)) = 0 := by
    have hcm : (∫ x in (0:ℝ)..L, (1 / L)
          * Real.cos (↑(k - n) * Real.pi * x / L))
        = (1 / L) * ∫ x in (0:ℝ)..L,
          Real.cos (↑(k - n) * Real.pi * x / L) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm, cos_integral_pos (k - n) L hd hL, mul_zero]
  have e2 : (∫ x in (0:ℝ)..L, (1 / L)
      * Real.cos (↑(n + k) * Real.pi * x / L)) = 0 := by
    have hcm : (∫ x in (0:ℝ)..L, (1 / L)
          * Real.cos (↑(n + k) * Real.pi * x / L))
        = (1 / L) * ∫ x in (0:ℝ)..L,
          Real.cos (↑(n + k) * Real.pi * x / L) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm, cos_integral_pos (n + k) L (by omega) hL, mul_zero]
  rw [hsub, e1, e2, sub_zero]

/-- Off-diagonal orthonormality for `n ≠ k` (the `n > k` case follows from
the `n < k` case by symmetry of the integrand). -/
lemma box_orthonormality_offdiag (n k : ℕ) (L : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hne : n ≠ k) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, boxFunction n L x * boxFunction k L x = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact box_orthonormality_offdiag_lt n k L hn hk hlt hL
  · have hsym : (fun x : ℝ => boxFunction n L x * boxFunction k L x)
        = (fun x : ℝ => boxFunction k L x * boxFunction n L x) := by
      funext x
      ring
    rw [hsym]
    exact box_orthonormality_offdiag_lt k n L hk hn hgt hL

/-- Orthonormality on `(0, L)`: the integral is `1` if `n = k`, else `0`. -/
lemma box_orthonormality (n k : ℕ) (L : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, boxFunction n L x * boxFunction k L x
      = if n = k then 1 else 0 := by
  by_cases h : n = k
  · rw [ite_eq_left h, h]
    exact box_orthonormality_diag k L hk hL
  · rw [ite_eq_right h]
    exact box_orthonormality_offdiag n k L hn hk h hL

/-! ## Section B: harmonic oscillator (low-lying states). -/

/-- Derivative of the real-to-complex coercion on `id`
(Mathlib `HasDerivAt.ofReal_comp`). -/
private lemma hasDerivAt_coe_id (x : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
  simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id x).ofReal_comp

/-- Transfer of `HasDerivAt` across the real-to-complex coercion
(Mathlib `HasDerivAt.ofReal_comp`). -/
private lemma ofReal_hasDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ)
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => ((f x : ℝ) : ℂ)) ((f' : ℝ) : ℂ) x :=
  h.ofReal_comp

/-- Ground-state normalization `π^(-1/4)`, via nested square roots. -/
noncomputable def oscC0 : ℝ := 1 / Real.sqrt (Real.sqrt Real.pi)

/-- Oscillator ground state `ψ_0` in `ħ = m = ω = 1` units. -/
noncomputable def oscFun0 (x : ℝ) : ℂ := ↑(oscC0 * Real.exp (-(x ^ 2) / 2))

/-- Oscillator eigen-equation for `v = 0` in `ħ = m = ω = 1` units:
`-(1/2) ψ_0'' + (1/2) x^2 ψ_0 = (1/2) ψ_0`. -/
lemma osc_eigen_0 (x : ℝ) :
    -(1 / 2) * deriv (deriv oscFun0) x
        + (1 / 2) * ((x ^ 2 : ℝ) : ℂ) * oscFun0 x
      = (1 / 2) * oscFun0 x := by
  have hg0 : ∀ y : ℝ, HasDerivAt (fun x : ℝ => oscC0 * Real.exp (-(x ^ 2) / 2))
      (-(y * (oscC0 * Real.exp (-(y ^ 2) / 2)))) y := by
    intro y
    have h0 :=
      (((hasDerivAt_pow 2 y).neg.div_const 2).exp.const_mul oscC0)
    convert h0 using 1
    all_goals try funext z
    all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq, zero_mul,
      mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub,
      sub_self, neg_zero]
    all_goals try field_simp
    all_goals try ring
  have hg1 : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => -(x * (oscC0 * Real.exp (-(x ^ 2) / 2))))
      (((y ^ 2 - 1)) * (oscC0 * Real.exp (-(y ^ 2) / 2))) y := by
    intro y
    have h0 := ((hasDerivAt_id y).mul
        (((hasDerivAt_pow 2 y).neg.div_const 2).exp.const_mul oscC0)).neg
    convert h0 using 1
    all_goals try funext z
    all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq, zero_mul,
      mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub,
      sub_self, neg_zero]
    all_goals try field_simp
    all_goals try ring
  have hF1 : deriv oscFun0
      = fun x : ℝ => ↑(-(x * (oscC0 * Real.exp (-(x ^ 2) / 2)))) := by
    funext y
    show deriv oscFun0 y = ↑(-(y * (oscC0 * Real.exp (-(y ^ 2) / 2))))
    exact (ofReal_hasDerivAt _ _ y (hg0 y)).deriv
  have hF2 : deriv (deriv oscFun0) x
      = ↑((((x ^ 2 - 1)) * (oscC0 * Real.exp (-(x ^ 2) / 2))) : ℝ) := by
    rw [hF1]
    exact (ofReal_hasDerivAt _ _ x (hg1 x)).deriv
  have hpt : oscFun0 x = ↑(oscC0 * Real.exp (-(x ^ 2) / 2)) := rfl
  rw [hF2, hpt]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_zero]
  ring

/-- Oscillator first excited state `ψ_1` in `ħ = m = ω = 1` units. -/
noncomputable def oscFun1 (x : ℝ) : ℂ :=
  ↑((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2)))

/-- Oscillator eigen-equation for `v = 1` in `ħ = m = ω = 1` units:
`-(1/2) ψ_1'' + (1/2) x^2 ψ_1 = (3/2) ψ_1`. -/
lemma osc_eigen_1 (x : ℝ) :
    -(1 / 2) * deriv (deriv oscFun1) x
        + (1 / 2) * ((x ^ 2 : ℝ) : ℂ) * oscFun1 x
      = (3 / 2) * oscFun1 x := by
  have hg0 : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => (Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2)))
      ((Real.sqrt 2 * oscC0)
        * ((1 - y ^ 2) * Real.exp (-(y ^ 2) / 2))) y := by
    intro y
    have h0 :=
      (((hasDerivAt_id y).mul
        (((hasDerivAt_pow 2 y).neg.div_const 2).exp)).const_mul
        (Real.sqrt 2 * oscC0))
    convert h0 using 1
    all_goals try funext z
    all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq, zero_mul,
      mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub,
      sub_self, neg_zero]
    all_goals try field_simp
    all_goals try ring
  have hg1 : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => (Real.sqrt 2 * oscC0)
        * ((1 - x ^ 2) * Real.exp (-(x ^ 2) / 2)))
      ((Real.sqrt 2 * oscC0)
        * ((y ^ 3 - 3 * y) * Real.exp (-(y ^ 2) / 2))) y := by
    intro y
    have h0 :=
      ((((hasDerivAt_const y 1).sub (hasDerivAt_pow 2 y)).mul
        (((hasDerivAt_pow 2 y).neg.div_const 2).exp)).const_mul
        (Real.sqrt 2 * oscC0))
    convert h0 using 1
    all_goals try funext z
    all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq, zero_mul,
      mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub,
      sub_self, neg_zero]
    all_goals try field_simp
    all_goals try ring
  have hF1 : deriv oscFun1 = fun x : ℝ => ↑(((Real.sqrt 2 * oscC0)
      * ((1 - x ^ 2) * Real.exp (-(x ^ 2) / 2))) : ℝ) := by
    funext y
    show deriv oscFun1 y = ↑(((Real.sqrt 2 * oscC0)
      * ((1 - y ^ 2) * Real.exp (-(y ^ 2) / 2))) : ℝ)
    exact (ofReal_hasDerivAt _ _ y (hg0 y)).deriv
  have hF2 : deriv (deriv oscFun1) x = ↑(((Real.sqrt 2 * oscC0)
      * ((x ^ 3 - 3 * x) * Real.exp (-(x ^ 2) / 2))) : ℝ) := by
    rw [hF1]
    exact (ofReal_hasDerivAt _ _ x (hg1 x)).deriv
  have hpt : oscFun1 x
      = ↑(((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2))) : ℝ) := rfl
  rw [hF2, hpt]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_zero]
  push_cast
  try ring

/-- Oscillator second excited state `ψ_2` in `ħ = m = ω = 1` units. -/
noncomputable def oscFun2 (x : ℝ) : ℂ :=
  ↑((((1 / Real.sqrt 2) * oscC0)
    * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))) : ℝ)

/-- Oscillator eigen-equation for `v = 2` in `ħ = m = ω = 1` units:
`-(1/2) ψ_2'' + (1/2) x^2 ψ_2 = (5/2) ψ_2`. -/
lemma osc_eigen_2 (x : ℝ) :
    -(1 / 2) * deriv (deriv oscFun2) x
        + (1 / 2) * ((x ^ 2 : ℝ) : ℂ) * oscFun2 x
      = (5 / 2) * oscFun2 x := by
  have hg0 : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => ((1 / Real.sqrt 2) * oscC0)
        * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)))
      (((1 / Real.sqrt 2) * oscC0)
        * ((5 * y - 2 * y ^ 3) * Real.exp (-(y ^ 2) / 2))) y := by
    intro y
    have h0 :=
      (((((hasDerivAt_pow 2 y).const_mul 2).sub (hasDerivAt_const y 1)).mul
        (((hasDerivAt_pow 2 y).neg.div_const 2).exp)).const_mul
        ((1 / Real.sqrt 2) * oscC0))
    convert h0 using 1
    all_goals try funext z
    all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq, zero_mul,
      mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub,
      sub_self, neg_zero]
    all_goals try field_simp
    all_goals try ring
  have hg1 : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => ((1 / Real.sqrt 2) * oscC0)
        * ((5 * x - 2 * x ^ 3) * Real.exp (-(x ^ 2) / 2)))
      (((1 / Real.sqrt 2) * oscC0)
        * ((2 * y ^ 4 - 11 * y ^ 2 + 5) * Real.exp (-(y ^ 2) / 2))) y := by
    intro y
    have h0 :=
      (((((hasDerivAt_id y).const_mul 5).sub
        ((hasDerivAt_pow 3 y).const_mul 2)).mul
        (((hasDerivAt_pow 2 y).neg.div_const 2).exp)).const_mul
        ((1 / Real.sqrt 2) * oscC0))
    convert h0 using 1
    all_goals try funext z
    all_goals try simp only [show (3:ℕ) - 1 = 2 from by decide,
      show (2:ℕ) - 1 = 1 from by decide, pow_one, Nat.cast_ofNat,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq, zero_mul,
      mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub,
      sub_self, neg_zero]
    all_goals try field_simp
    all_goals try ring
  have hF1 : deriv oscFun2 = fun x : ℝ => ↑((((1 / Real.sqrt 2) * oscC0)
      * ((5 * x - 2 * x ^ 3) * Real.exp (-(x ^ 2) / 2))) : ℝ) := by
    funext y
    show deriv oscFun2 y = ↑((((1 / Real.sqrt 2) * oscC0)
      * ((5 * y - 2 * y ^ 3) * Real.exp (-(y ^ 2) / 2))) : ℝ)
    exact (ofReal_hasDerivAt _ _ y (hg0 y)).deriv
  have hF2 : deriv (deriv oscFun2) x = ↑((((1 / Real.sqrt 2) * oscC0)
      * ((2 * x ^ 4 - 11 * x ^ 2 + 5) * Real.exp (-(x ^ 2) / 2))) : ℝ) := by
    rw [hF1]
    exact (ofReal_hasDerivAt _ _ x (hg1 x)).deriv
  have hpt : oscFun2 x = ↑((((1 / Real.sqrt 2) * oscC0)
      * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))) : ℝ) := rfl
  rw [hF2, hpt]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one,
    Complex.ofReal_zero]
  push_cast
  try ring

/-- Base Gaussian integral `∫ x, exp (-x^2) = √π` (Mathlib
`integral_gaussian`). -/
lemma gaussian_moment_zero :
    ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
  have h : ∫ x : ℝ, Real.exp (-(1:ℝ) * x ^ 2)
      = Real.sqrt (Real.pi / 1) :=
    integral_gaussian 1
  simpa using h

/-- Oscillator `(0, 0)` orthonormality from the base Gaussian integral
(Mathlib `MeasureTheory.integral_const_mul`, `integral_complex_ofReal`). -/
lemma osc_orthonormality_00 : ∫ x : ℝ, oscFun0 x * oscFun0 x = 1 := by
  have hsq : oscC0 ^ 2 = 1 / Real.sqrt Real.pi := by
    unfold oscC0
    rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hfun : (fun x : ℝ => oscFun0 x * oscFun0 x)
      = (fun x : ℝ =>
        ((1 / Real.sqrt Real.pi * Real.exp (-x ^ 2) : ℝ) : ℂ)) := by
    funext x
    have hpt : oscFun0 x = ↑(oscC0 * Real.exp (-(x ^ 2) / 2)) := rfl
    rw [hpt, ← Complex.ofReal_mul]
    congr 1
    have hexp : (Real.exp (-(x ^ 2) / 2)) ^ 2 = Real.exp (-x ^ 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc (oscC0 * Real.exp (-(x ^ 2) / 2))
            * (oscC0 * Real.exp (-(x ^ 2) / 2))
        = (oscC0 ^ 2) * ((Real.exp (-(x ^ 2) / 2)) ^ 2) := by ring
      _ = (1 / Real.sqrt Real.pi) * Real.exp (-x ^ 2) := by rw [hsq, hexp]
  have hcm : (∫ x : ℝ, 1 / Real.sqrt Real.pi * Real.exp (-x ^ 2))
      = (1 / Real.sqrt Real.pi) * ∫ x : ℝ, Real.exp (-x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  have hpi : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hreal : (1 / Real.sqrt Real.pi : ℝ) * Real.sqrt Real.pi = 1 := by
    field_simp
    try ring
  rw [hfun, integral_complex_ofReal, hcm, gaussian_moment_zero, hreal,
    Complex.ofReal_one]

/-- Odd real functions integrate to zero over the whole line, by negation
symmetry (Mathlib `MeasureTheory.integral_neg_eq_self`,
`MeasureTheory.integral_neg`). -/
private lemma integral_odd_vanishes {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    ∫ x : ℝ, f x = 0 := by
  have hneg : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x :=
    MeasureTheory.integral_neg_eq_self f _
  have hfun : (fun x : ℝ => f (-x)) = fun x : ℝ => -f x := funext hf
  have hodd : (∫ x : ℝ, f (-x)) = -(∫ x : ℝ, f x) := by
    rw [hfun, MeasureTheory.integral_neg]
  linarith

/-- Integrability of `x^n * exp (-x^2)` over the whole line (Mathlib
`integrable_rpow_mul_exp_neg_mul_sq`). -/
private lemma integrable_pow_mul_exp_neg_sq (n : ℕ) :
    MeasureTheory.Integrable fun x : ℝ => x ^ n * Real.exp (-x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := (n : ℝ))
    (by norm_num) (by have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
  have hfun : (fun x : ℝ => x ^ n * Real.exp (-x ^ 2))
      = fun x : ℝ => x ^ (n : ℝ) * Real.exp (-1 * x ^ 2) := by
    funext x
    have hrw : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n
    have hexp : (-1 : ℝ) * x ^ 2 = -x ^ 2 := by ring
    rw [hrw, hexp]
  rw [hfun]
  exact h

/-- Integrability of `exp (-x^2)` over the whole line (Mathlib
`integrable_exp_neg_mul_sq`). -/
private lemma integrable_exp_neg_sq :
    MeasureTheory.Integrable fun x : ℝ => Real.exp (-x ^ 2) := by
  have h := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hfun : (fun x : ℝ => Real.exp (-x ^ 2))
      = fun x : ℝ => Real.exp (-1 * x ^ 2) := by
    funext x
    congr 1
    ring
  rw [hfun]
  exact h

/-- First Gaussian moment `∫ x, x * exp (-x^2) = 0` by oddness. -/
private lemma gaussian_moment_one :
    ∫ x : ℝ, x * Real.exp (-x ^ 2) = 0 := by
  apply integral_odd_vanishes
  intro x
  show (-x) * Real.exp (-(-x) ^ 2) = -(x * Real.exp (-x ^ 2))
  have h2 : (-x) ^ 2 = x ^ 2 := by ring
  rw [h2]
  ring

/-- Second Gaussian moment `∫ x, x^2 * exp (-x^2) = √π / 2` by
integration by parts (Mathlib
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`). -/
private lemma gaussian_moment_two :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  have hexp : ∀ y : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2))
      (Real.exp (-y ^ 2) * (-2 * y)) y := by
    intro y
    have h0 := ((hasDerivAt_pow 2 y).neg.exp)
    convert h0 using 1
    simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one,
      Nat.cast_ofNat, Pi.neg_apply]
    ring
  have hv : ∀ x ∈ tsupport (fun x : ℝ => x),
      HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
      (x * Real.exp (-x ^ 2)) x := by
    intro x _
    have h0 := (hexp x).neg.div_const 2
    convert h0 using 1
    ring
  have hu : ∀ x ∈ tsupport (fun x : ℝ => -Real.exp (-x ^ 2) / 2),
      HasDerivAt (fun x : ℝ => x) 1 x := by
    intro x _
    exact hasDerivAt_id x
  have huv' : MeasureTheory.Integrable
      ((fun x : ℝ => x) * (fun x : ℝ => x * Real.exp (-x ^ 2))) := by
    have hfun : (fun x : ℝ => x) * (fun x : ℝ => x * Real.exp (-x ^ 2))
        = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
      funext x
      simp only [Pi.mul_apply]
      show x * (x * Real.exp (-x ^ 2)) = x ^ 2 * Real.exp (-x ^ 2)
      ring
    rw [hfun]
    exact integrable_pow_mul_exp_neg_sq 2
  have hu'v : MeasureTheory.Integrable
      ((fun _ : ℝ => (1:ℝ)) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)) := by
    have hfun : (fun _ : ℝ => (1:ℝ)) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
        = fun x : ℝ => (-1 / 2) * Real.exp (-x ^ 2) := by
      funext x
      simp only [Pi.mul_apply]
      show (1:ℝ) * (-Real.exp (-x ^ 2) / 2) = (-1 / 2) * Real.exp (-x ^ 2)
      ring
    rw [hfun]
    exact integrable_exp_neg_sq.const_mul _
  have huv : MeasureTheory.Integrable
      ((fun x : ℝ => x) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)) := by
    have h1 : MeasureTheory.Integrable fun x : ℝ => x * Real.exp (-x ^ 2) := by
      have h := integrable_pow_mul_exp_neg_sq 1
      simpa using h
    have hfun : (fun x : ℝ => x) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
        = fun x : ℝ => (-1 / 2) * (x * Real.exp (-x ^ 2)) := by
      funext x
      simp only [Pi.mul_apply]
      show x * (-Real.exp (-x ^ 2) / 2) = (-1 / 2) * (x * Real.exp (-x ^ 2))
      ring
    rw [hfun]
    exact h1.const_mul _
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1:ℝ))
    (v := fun x : ℝ => -Real.exp (-x ^ 2) / 2)
    (v' := fun x : ℝ => x * Real.exp (-x ^ 2)) hu hv huv' hu'v huv
  have hibp2 : (∫ x : ℝ, x * (x * Real.exp (-x ^ 2)))
      = -∫ x : ℝ, (1:ℝ) * (-Real.exp (-x ^ 2) / 2) := hibp
  have hfun_lhs : (fun x : ℝ => x * (x * Real.exp (-x ^ 2)))
      = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
    funext x
    ring
  have hrhs : (∫ x : ℝ, (1:ℝ) * (-Real.exp (-x ^ 2) / 2))
      = (-1 / 2) * Real.sqrt Real.pi := by
    have hfun_rhs : (fun x : ℝ => (1:ℝ) * (-Real.exp (-x ^ 2) / 2))
        = fun x : ℝ => (-1 / 2) * Real.exp (-x ^ 2) := by
      funext x
      ring
    rw [hfun_rhs, MeasureTheory.integral_const_mul, gaussian_moment_zero]
  rw [hfun_lhs] at hibp2
  rw [hrhs] at hibp2
  have hval : -((-1 / 2 : ℝ) * Real.sqrt Real.pi) = Real.sqrt Real.pi / 2 := by
    ring
  rw [hval] at hibp2
  exact hibp2

/-- Third Gaussian moment `∫ x, x^3 * exp (-x^2) = 0` by oddness. -/
private lemma gaussian_moment_three :
    ∫ x : ℝ, x ^ 3 * Real.exp (-x ^ 2) = 0 := by
  apply integral_odd_vanishes
  intro x
  show (-x) ^ 3 * Real.exp (-(-x) ^ 2) = -(x ^ 3 * Real.exp (-x ^ 2))
  have h2 : (-x) ^ 2 = x ^ 2 := by ring
  rw [h2]
  ring

/-- Fourth Gaussian moment `∫ x, x^4 * exp (-x^2) = 3√π / 4` by
integration by parts from the second moment. -/
private lemma gaussian_moment_four :
    ∫ x : ℝ, x ^ 4 * Real.exp (-x ^ 2) = 3 * Real.sqrt Real.pi / 4 := by
  have hexp : ∀ y : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2))
      (Real.exp (-y ^ 2) * (-2 * y)) y := by
    intro y
    have h0 := ((hasDerivAt_pow 2 y).neg.exp)
    convert h0 using 1
    simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one,
      Nat.cast_ofNat, Pi.neg_apply]
    ring
  have hv : ∀ x ∈ tsupport (fun x : ℝ => x ^ 3),
      HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
      (x * Real.exp (-x ^ 2)) x := by
    intro x _
    have h0 := (hexp x).neg.div_const 2
    convert h0 using 1
    ring
  have hu : ∀ x ∈ tsupport (fun x : ℝ => -Real.exp (-x ^ 2) / 2),
      HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    intro x _
    exact hasDerivAt_pow 3 x
  have huv' : MeasureTheory.Integrable
      ((fun x : ℝ => x ^ 3) * (fun x : ℝ => x * Real.exp (-x ^ 2))) := by
    have hfun : (fun x : ℝ => x ^ 3) * (fun x : ℝ => x * Real.exp (-x ^ 2))
        = fun x : ℝ => x ^ 4 * Real.exp (-x ^ 2) := by
      funext x
      simp only [Pi.mul_apply]
      show x ^ 3 * (x * Real.exp (-x ^ 2)) = x ^ 4 * Real.exp (-x ^ 2)
      ring
    rw [hfun]
    exact integrable_pow_mul_exp_neg_sq 4
  have hu'v : MeasureTheory.Integrable
      ((fun x : ℝ => 3 * x ^ 2) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)) := by
    have hfun : (fun x : ℝ => 3 * x ^ 2) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
        = fun x : ℝ => (-3 / 2) * (x ^ 2 * Real.exp (-x ^ 2)) := by
      funext x
      simp only [Pi.mul_apply]
      show (3 * x ^ 2) * (-Real.exp (-x ^ 2) / 2)
        = (-3 / 2) * (x ^ 2 * Real.exp (-x ^ 2))
      ring
    rw [hfun]
    exact (integrable_pow_mul_exp_neg_sq 2).const_mul _
  have huv : MeasureTheory.Integrable
      ((fun x : ℝ => x ^ 3) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)) := by
    have hfun : (fun x : ℝ => x ^ 3) * (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
        = fun x : ℝ => (-1 / 2) * (x ^ 3 * Real.exp (-x ^ 2)) := by
      funext x
      simp only [Pi.mul_apply]
      show x ^ 3 * (-Real.exp (-x ^ 2) / 2)
        = (-1 / 2) * (x ^ 3 * Real.exp (-x ^ 2))
      ring
    rw [hfun]
    exact (integrable_pow_mul_exp_neg_sq 3).const_mul _
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ 3) (u' := fun x : ℝ => 3 * x ^ 2)
    (v := fun x : ℝ => -Real.exp (-x ^ 2) / 2)
    (v' := fun x : ℝ => x * Real.exp (-x ^ 2)) hu hv huv' hu'v huv
  have hibp2 : (∫ x : ℝ, x ^ 3 * (x * Real.exp (-x ^ 2)))
      = -∫ x : ℝ, (3 * x ^ 2) * (-Real.exp (-x ^ 2) / 2) := hibp
  have hfun_lhs : (fun x : ℝ => x ^ 3 * (x * Real.exp (-x ^ 2)))
      = fun x : ℝ => x ^ 4 * Real.exp (-x ^ 2) := by
    funext x
    ring
  have hrhs : (∫ x : ℝ, (3 * x ^ 2) * (-Real.exp (-x ^ 2) / 2))
      = (-3 / 2) * (Real.sqrt Real.pi / 2) := by
    have hfun_rhs : (fun x : ℝ => (3 * x ^ 2) * (-Real.exp (-x ^ 2) / 2))
        = fun x : ℝ => (-3 / 2) * (x ^ 2 * Real.exp (-x ^ 2)) := by
      funext x
      ring
    rw [hfun_rhs, MeasureTheory.integral_const_mul, gaussian_moment_two]
  rw [hfun_lhs] at hibp2
  rw [hrhs] at hibp2
  have hval : -((-3 / 2 : ℝ) * (Real.sqrt Real.pi / 2))
      = 3 * Real.sqrt Real.pi / 4 := by
    ring
  rw [hval] at hibp2
  exact hibp2

/-- Oscillator `(0, 1)` orthonormality: the product integrand is odd, so
the integral vanishes by the first Gaussian moment. -/
lemma osc_orthonormality_01 : ∫ x : ℝ, oscFun0 x * oscFun1 x = 0 := by
  have hsq : oscC0 * (Real.sqrt 2 * oscC0)
      = Real.sqrt 2 * (1 / Real.sqrt Real.pi) := by
    have h2 : oscC0 ^ 2 = 1 / Real.sqrt Real.pi := by
      unfold oscC0
      rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    calc oscC0 * (Real.sqrt 2 * oscC0)
        = Real.sqrt 2 * oscC0 ^ 2 := by ring
      _ = Real.sqrt 2 * (1 / Real.sqrt Real.pi) := by rw [h2]
  have hfun : (fun x : ℝ => oscFun0 x * oscFun1 x)
      = (fun x : ℝ => (((Real.sqrt 2 * (1 / Real.sqrt Real.pi))
        * (x * Real.exp (-x ^ 2)) : ℝ) : ℂ)) := by
    funext x
    have h0 : oscFun0 x = ↑(oscC0 * Real.exp (-(x ^ 2) / 2)) := rfl
    have h1 : oscFun1 x
        = ↑((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2))) := rfl
    rw [h0, h1, ← Complex.ofReal_mul]
    congr 1
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)
        = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (oscC0 * Real.exp (-(x ^ 2) / 2))
            * ((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2)))
        = (oscC0 * (Real.sqrt 2 * oscC0))
          * (x * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2))) := by
          ring
      _ = (Real.sqrt 2 * (1 / Real.sqrt Real.pi))
          * (x * Real.exp (-x ^ 2)) := by rw [hsq, hexp]
  have hcm : (∫ x : ℝ, (Real.sqrt 2 * (1 / Real.sqrt Real.pi))
        * (x * Real.exp (-x ^ 2)))
      = (Real.sqrt 2 * (1 / Real.sqrt Real.pi))
        * ∫ x : ℝ, x * Real.exp (-x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  rw [hfun, integral_complex_ofReal, hcm, gaussian_moment_one, mul_zero,
    Complex.ofReal_zero]

/-- Oscillator `(1, 0)` orthonormality, by commutativity from `(0, 1)`. -/
lemma osc_orthonormality_10 : ∫ x : ℝ, oscFun1 x * oscFun0 x = 0 := by
  have hfun : (fun x : ℝ => oscFun1 x * oscFun0 x)
      = fun x : ℝ => oscFun0 x * oscFun1 x := by
    funext x
    ring
  rw [hfun]
  exact osc_orthonormality_01

/-- Oscillator `(1, 1)` orthonormality from the second Gaussian moment
(this diagonal pins the `√2 * oscC0` normalization). -/
lemma osc_orthonormality_11 : ∫ x : ℝ, oscFun1 x * oscFun1 x = 1 := by
  have hsq : (Real.sqrt 2 * oscC0) ^ 2 = 2 / Real.sqrt Real.pi := by
    unfold oscC0
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    ring
  have hfun : (fun x : ℝ => oscFun1 x * oscFun1 x)
      = (fun x : ℝ =>
        ((2 / Real.sqrt Real.pi * (x ^ 2 * Real.exp (-x ^ 2)) : ℝ) : ℂ)) := by
    funext x
    have hpt : oscFun1 x
        = ↑((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2))) := rfl
    rw [hpt, ← Complex.ofReal_mul]
    congr 1
    have hexp : (Real.exp (-(x ^ 2) / 2)) ^ 2 = Real.exp (-x ^ 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc ((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2)))
            * ((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2)))
        = ((Real.sqrt 2 * oscC0) ^ 2)
          * (x ^ 2 * (Real.exp (-(x ^ 2) / 2)) ^ 2) := by ring
      _ = (2 / Real.sqrt Real.pi) * (x ^ 2 * Real.exp (-x ^ 2)) := by
        rw [hsq, hexp]
  have hcm : (∫ x : ℝ, 2 / Real.sqrt Real.pi * (x ^ 2 * Real.exp (-x ^ 2)))
      = (2 / Real.sqrt Real.pi) * ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  have hreal : (2 / Real.sqrt Real.pi : ℝ) * (Real.sqrt Real.pi / 2) = 1 := by
    have hpi : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
    try ring
  rw [hfun, integral_complex_ofReal, hcm, gaussian_moment_two, hreal,
    Complex.ofReal_one]

/-- Oscillator `(0, 2)` orthonormality: `∫ (2x^2-1)·e^(-x^2) = 0`
from the zeroth and second Gaussian moments. -/
lemma osc_orthonormality_02 : ∫ x : ℝ, oscFun0 x * oscFun2 x = 0 := by
  have hsq : oscC0 * ((1 / Real.sqrt 2) * oscC0)
      = (1 / Real.sqrt 2) * (1 / Real.sqrt Real.pi) := by
    have h2 : oscC0 ^ 2 = 1 / Real.sqrt Real.pi := by
      unfold oscC0
      rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    calc oscC0 * ((1 / Real.sqrt 2) * oscC0)
        = (1 / Real.sqrt 2) * oscC0 ^ 2 := by ring
      _ = (1 / Real.sqrt 2) * (1 / Real.sqrt Real.pi) := by rw [h2]
  have hfun : (fun x : ℝ => oscFun0 x * oscFun2 x)
      = (fun x : ℝ => ((((1 / Real.sqrt 2) * (1 / Real.sqrt Real.pi))
        * ((2 * x ^ 2 - 1) * Real.exp (-x ^ 2)) : ℝ) : ℂ)) := by
    funext x
    have h0 : oscFun0 x = ↑(oscC0 * Real.exp (-(x ^ 2) / 2)) := rfl
    have h2 : oscFun2 x = ↑((((1 / Real.sqrt 2) * oscC0)
        * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))) : ℝ) := rfl
    rw [h0, h2, ← Complex.ofReal_mul]
    congr 1
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)
        = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (oscC0 * Real.exp (-(x ^ 2) / 2))
            * (((1 / Real.sqrt 2) * oscC0)
              * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)))
        = (oscC0 * ((1 / Real.sqrt 2) * oscC0))
          * ((2 * x ^ 2 - 1)
            * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2))) := by
          ring
      _ = ((1 / Real.sqrt 2) * (1 / Real.sqrt Real.pi))
          * ((2 * x ^ 2 - 1) * Real.exp (-x ^ 2)) := by rw [hsq, hexp]
  have hcm : (∫ x : ℝ, ((1 / Real.sqrt 2) * (1 / Real.sqrt Real.pi))
        * ((2 * x ^ 2 - 1) * Real.exp (-x ^ 2)))
      = ((1 / Real.sqrt 2) * (1 / Real.sqrt Real.pi))
        * ∫ x : ℝ, (2 * x ^ 2 - 1) * Real.exp (-x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  have hsplit : (∫ x : ℝ, (2 * x ^ 2 - 1) * Real.exp (-x ^ 2))
      = 2 * (∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2))
        - ∫ x : ℝ, Real.exp (-x ^ 2) := by
    have hfun2 : (fun x : ℝ => (2 * x ^ 2 - 1) * Real.exp (-x ^ 2))
        = fun x : ℝ => 2 * (x ^ 2 * Real.exp (-x ^ 2))
          - Real.exp (-x ^ 2) := by
      funext x
      ring
    have h2i : MeasureTheory.Integrable
        fun x : ℝ => 2 * (x ^ 2 * Real.exp (-x ^ 2)) :=
      (integrable_pow_mul_exp_neg_sq 2).const_mul 2
    rw [hfun2, MeasureTheory.integral_sub h2i integrable_exp_neg_sq,
      MeasureTheory.integral_const_mul 2 _]
  have hS : 2 * (Real.sqrt Real.pi / 2) - Real.sqrt Real.pi = 0 := by
    ring
  rw [hfun, integral_complex_ofReal, hcm, hsplit, gaussian_moment_two,
    gaussian_moment_zero, hS, mul_zero, Complex.ofReal_zero]

/-- Oscillator `(2, 0)` orthonormality, by commutativity from `(0, 2)`. -/
lemma osc_orthonormality_20 : ∫ x : ℝ, oscFun2 x * oscFun0 x = 0 := by
  have hfun : (fun x : ℝ => oscFun2 x * oscFun0 x)
      = fun x : ℝ => oscFun0 x * oscFun2 x := by
    funext x
    ring
  rw [hfun]
  exact osc_orthonormality_02

/-- Oscillator `(1, 2)` orthonormality: `∫ (2x^3-x)·e^(-x^2) = 0`
from the first and third Gaussian moments. -/
lemma osc_orthonormality_12 : ∫ x : ℝ, oscFun1 x * oscFun2 x = 0 := by
  have hsq : (Real.sqrt 2 * oscC0) * ((1 / Real.sqrt 2) * oscC0)
      = 1 / Real.sqrt Real.pi := by
    have h2 : oscC0 ^ 2 = 1 / Real.sqrt Real.pi := by
      unfold oscC0
      rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hsqrt : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
      have h2ne : Real.sqrt 2 ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
      rw [mul_one_div, div_self h2ne]
    calc (Real.sqrt 2 * oscC0) * ((1 / Real.sqrt 2) * oscC0)
        = (Real.sqrt 2 * (1 / Real.sqrt 2)) * oscC0 ^ 2 := by ring
      _ = 1 / Real.sqrt Real.pi := by rw [hsqrt, h2, one_mul]
  have hfun : (fun x : ℝ => oscFun1 x * oscFun2 x)
      = (fun x : ℝ => (((1 / Real.sqrt Real.pi)
        * ((2 * x ^ 3 - x) * Real.exp (-x ^ 2)) : ℝ) : ℂ)) := by
    funext x
    have h1 : oscFun1 x
        = ↑((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2))) := rfl
    have h2 : oscFun2 x = ↑((((1 / Real.sqrt 2) * oscC0)
        * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))) : ℝ) := rfl
    rw [h1, h2, ← Complex.ofReal_mul]
    congr 1
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)
        = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ((Real.sqrt 2 * oscC0) * (x * Real.exp (-(x ^ 2) / 2)))
            * (((1 / Real.sqrt 2) * oscC0)
              * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)))
        = ((Real.sqrt 2 * oscC0) * ((1 / Real.sqrt 2) * oscC0))
          * ((2 * x ^ 3 - x)
            * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2))) := by
          ring
      _ = (1 / Real.sqrt Real.pi)
          * ((2 * x ^ 3 - x) * Real.exp (-x ^ 2)) := by rw [hsq, hexp]
  have hcm : (∫ x : ℝ, (1 / Real.sqrt Real.pi)
        * ((2 * x ^ 3 - x) * Real.exp (-x ^ 2)))
      = (1 / Real.sqrt Real.pi)
        * ∫ x : ℝ, (2 * x ^ 3 - x) * Real.exp (-x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  have hsplit : (∫ x : ℝ, (2 * x ^ 3 - x) * Real.exp (-x ^ 2))
      = 2 * (∫ x : ℝ, x ^ 3 * Real.exp (-x ^ 2))
        - ∫ x : ℝ, x * Real.exp (-x ^ 2) := by
    have hfun2 : (fun x : ℝ => (2 * x ^ 3 - x) * Real.exp (-x ^ 2))
        = fun x : ℝ => 2 * (x ^ 3 * Real.exp (-x ^ 2))
          - x * Real.exp (-x ^ 2) := by
      funext x
      ring
    have h3i : MeasureTheory.Integrable
        fun x : ℝ => 2 * (x ^ 3 * Real.exp (-x ^ 2)) :=
      (integrable_pow_mul_exp_neg_sq 3).const_mul 2
    have h1i : MeasureTheory.Integrable
        fun x : ℝ => x * Real.exp (-x ^ 2) := by
      have h := integrable_pow_mul_exp_neg_sq 1
      simpa using h
    rw [hfun2, MeasureTheory.integral_sub h3i h1i,
      MeasureTheory.integral_const_mul 2 _]
  have hS : 2 * (0:ℝ) - 0 = 0 := by ring
  rw [hfun, integral_complex_ofReal, hcm, hsplit, gaussian_moment_three,
    gaussian_moment_one, hS, mul_zero, Complex.ofReal_zero]

/-- Oscillator `(2, 1)` orthonormality, by commutativity from `(1, 2)`. -/
lemma osc_orthonormality_21 : ∫ x : ℝ, oscFun2 x * oscFun1 x = 0 := by
  have hfun : (fun x : ℝ => oscFun2 x * oscFun1 x)
      = fun x : ℝ => oscFun1 x * oscFun2 x := by
    funext x
    ring
  rw [hfun]
  exact osc_orthonormality_12

/-- Oscillator `(2, 2)` orthonormality from the zeroth, second, and
fourth Gaussian moments (this diagonal pins the `(1/√2) * oscC0`
normalization). -/
lemma osc_orthonormality_22 : ∫ x : ℝ, oscFun2 x * oscFun2 x = 1 := by
  have hsq : ((1 / Real.sqrt 2) * oscC0) ^ 2
      = (1 / 2) * (1 / Real.sqrt Real.pi) := by
    have h2 : oscC0 ^ 2 = 1 / Real.sqrt Real.pi := by
      unfold oscC0
      rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hsqrt2 : ((1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow]
      have h2eq : (Real.sqrt 2) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      rw [h2eq]
    calc ((1 / Real.sqrt 2) * oscC0) ^ 2
        = ((1 / Real.sqrt 2) ^ 2) * oscC0 ^ 2 := by ring
      _ = (1 / 2) * (1 / Real.sqrt Real.pi) := by rw [hsqrt2, h2]
  have hfun : (fun x : ℝ => oscFun2 x * oscFun2 x)
      = (fun x : ℝ => ((((1 / 2) * (1 / Real.sqrt Real.pi))
        * (((2 * x ^ 2 - 1) ^ 2) * Real.exp (-x ^ 2)) : ℝ) : ℂ)) := by
    funext x
    have h2 : oscFun2 x = ↑((((1 / Real.sqrt 2) * oscC0)
        * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))) : ℝ) := rfl
    rw [h2, ← Complex.ofReal_mul]
    congr 1
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)
        = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (((1 / Real.sqrt 2) * oscC0)
            * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)))
            * (((1 / Real.sqrt 2) * oscC0)
              * ((2 * x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)))
        = (((1 / Real.sqrt 2) * oscC0) ^ 2)
          * (((2 * x ^ 2 - 1) ^ 2)
            * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2))) := by
          ring
      _ = ((1 / 2) * (1 / Real.sqrt Real.pi))
          * (((2 * x ^ 2 - 1) ^ 2) * Real.exp (-x ^ 2)) := by rw [hsq, hexp]
  have hcm : (∫ x : ℝ, ((1 / 2) * (1 / Real.sqrt Real.pi))
        * (((2 * x ^ 2 - 1) ^ 2) * Real.exp (-x ^ 2)))
      = ((1 / 2) * (1 / Real.sqrt Real.pi))
        * ∫ x : ℝ, ((2 * x ^ 2 - 1) ^ 2) * Real.exp (-x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  have hsplit : (∫ x : ℝ, ((2 * x ^ 2 - 1) ^ 2) * Real.exp (-x ^ 2))
      = 4 * (∫ x : ℝ, x ^ 4 * Real.exp (-x ^ 2))
        - 4 * (∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2))
        + ∫ x : ℝ, Real.exp (-x ^ 2) := by
    have hfun2 : (fun x : ℝ => ((2 * x ^ 2 - 1) ^ 2) * Real.exp (-x ^ 2))
        = fun x : ℝ => (4 * (x ^ 4 * Real.exp (-x ^ 2))
          - 4 * (x ^ 2 * Real.exp (-x ^ 2))) + Real.exp (-x ^ 2) := by
      funext x
      ring
    have h4i : MeasureTheory.Integrable
        fun x : ℝ => 4 * (x ^ 4 * Real.exp (-x ^ 2)) :=
      (integrable_pow_mul_exp_neg_sq 4).const_mul 4
    have h2i : MeasureTheory.Integrable
        fun x : ℝ => 4 * (x ^ 2 * Real.exp (-x ^ 2)) :=
      (integrable_pow_mul_exp_neg_sq 2).const_mul 4
    have hsub : MeasureTheory.Integrable
        fun x : ℝ => 4 * (x ^ 4 * Real.exp (-x ^ 2))
          - 4 * (x ^ 2 * Real.exp (-x ^ 2)) := h4i.sub h2i
    rw [hfun2, MeasureTheory.integral_add hsub integrable_exp_neg_sq,
      MeasureTheory.integral_sub h4i h2i,
      MeasureTheory.integral_const_mul 4 _,
      MeasureTheory.integral_const_mul 4 _]
  have hS : 4 * (3 * Real.sqrt Real.pi / 4) - 4 * (Real.sqrt Real.pi / 2)
      + Real.sqrt Real.pi = 2 * Real.sqrt Real.pi := by
    ring
  have hreal : ((1 / 2 : ℝ) * (1 / Real.sqrt Real.pi))
      * (2 * Real.sqrt Real.pi) = 1 := by
    have hpi : Real.sqrt Real.pi ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
    try ring
  rw [hfun, integral_complex_ofReal, hcm, hsplit, gaussian_moment_four,
    gaussian_moment_two, gaussian_moment_zero, hS, hreal, Complex.ofReal_one]

/-! ## Section C: ladder operators on Schwartz space; box moments. -/

/-- The Schwartz carrier: complex-valued functions on `ℝ` admitting a
Mathlib `SchwartzMap` representative. -/
def SchwartzCarrier : Set (ℝ → ℂ) :=
  {f | ∃ s : SchwartzMap ℝ ℂ, ⇑s = f}

/-- Annihilation function in `ħ = m = ω = 1` units:
`a f = (x ↦ (x * f x + deriv f x) / √2)`. -/
noncomputable def annFun (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (↑x * f x + deriv f x) / ↑(Real.sqrt 2)

/-- Creation function in `ħ = m = ω = 1` units:
`a† f = (x ↦ (x * f x - deriv f x) / √2)`. -/
noncomputable def creFun (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (↑x * f x - deriv f x) / ↑(Real.sqrt 2)

/-- Pointwise ladder identity `annFun (creFun f) x - creFun (annFun f) x = f x`, for any `f`
with first and second derivatives at `x`: a formal identity of the differential expressions
(by `deriv` arithmetic plus the product rule; Mathlib `HasDerivAt.mul`,
`HasDerivAt.add/sub/div_const`). -/
lemma ladder_commutator_pointwise_of_hasDerivAt (f : ℝ → ℂ) (df ddf : ℂ) (x : ℝ)
    (hf : HasDerivAt f df x) (hf' : HasDerivAt (deriv f) ddf x) :
    annFun (creFun f) x - creFun (annFun f) x = f x := by
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have h2nn : (0:ℝ) ≤ 2 := by norm_num
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h2nn]
    norm_num
  have hAf : HasDerivAt (fun x : ℝ => ↑x * f x) (1 * f x + ↑x * df) x := by
    have h0 := (hasDerivAt_coe_id x).mul hf
    convert h0 using 1
    all_goals try funext y
    all_goals try simp only [Pi.mul_apply]
    all_goals try field_simp
    all_goals try ring
  have hCre : HasDerivAt (creFun f)
      ((1 * f x + ↑x * df - ddf) / ↑(Real.sqrt 2)) x := by
    have h0 := (hAf.sub hf').div_const (↑(Real.sqrt 2))
    convert h0 using 1
    all_goals try funext y
    all_goals try simp only [creFun, annFun, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
      id_eq]
    all_goals try field_simp
    all_goals try ring
  have hAnn : HasDerivAt (annFun f)
      ((1 * f x + ↑x * df + ddf) / ↑(Real.sqrt 2)) x := by
    have h0 := (hAf.add hf').div_const (↑(Real.sqrt 2))
    convert h0 using 1
    all_goals try funext y
    all_goals try simp only [creFun, annFun, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
      id_eq]
    all_goals try field_simp
    all_goals try ring
  have hCrev : deriv (creFun f) x
      = (1 * f x + ↑x * df - ddf) / ↑(Real.sqrt 2) := hCre.deriv
  have hAnnv : deriv (annFun f) x
      = (1 * f x + ↑x * df + ddf) / ↑(Real.sqrt 2) := hAnn.deriv
  have hdf : deriv f x = df := hf.deriv
  have hCrePt : creFun f x
      = (↑x * f x - deriv f x) / ↑(Real.sqrt 2) := rfl
  have hAnnPt : annFun f x
      = (↑x * f x + deriv f x) / ↑(Real.sqrt 2) := rfl
  have hOut1 : annFun (creFun f) x
      = (↑x * (creFun f x) + deriv (creFun f) x) / ↑(Real.sqrt 2) := rfl
  have hOut2 : creFun (annFun f) x
      = (↑x * (annFun f x) - deriv (annFun f) x) / ↑(Real.sqrt 2) := rfl
  rw [hOut1, hOut2, hCrePt, hAnnPt, hCrev, hAnnv, hdf]
  simp only [← mul_div_assoc, ← add_div, ← sub_div, div_div, ← pow_two]
  rw [div_eq_iff (pow_ne_zero 2 hs), hsq]
  ring

/-- Pointwise ladder identity for Schwartz functions:
`annFun (creFun f) x - creFun (annFun f) x = f x` for every `f` in `SchwartzCarrier` (Mathlib
`SchwartzMap.smooth`, `ContDiff.deriv`). This is a formal identity of the differential
expressions `annFun` and `creFun`, not a commutator of the records `annihilation` and
`creation`: closure of the Schwartz carrier under `annFun`/`creFun` is not proved, so those
records cannot be composed. -/
lemma ladder_commutator_pointwise_schwartz (f : ℝ → ℂ) (hf : f ∈ SchwartzCarrier)
    (x : ℝ) :
    annFun (creFun f) x - creFun (annFun f) x = f x := by
  obtain ⟨s, hs⟩ := hf
  subst hs
  have hsm : ContDiff ℝ 2 (⇑s : ℝ → ℂ) := s.smooth 2
  have hf1 : HasDerivAt (⇑s : ℝ → ℂ) (deriv ⇑s x) x :=
    ((hsm.contDiffAt (x := x)).differentiableAt (by decide)).hasDerivAt
  have hderiv1 : ContDiff ℝ 1 (deriv ⇑s) :=
    hsm.deriv'
  have hf2 : HasDerivAt (deriv ⇑s) (deriv (deriv ⇑s) x) x :=
    ((hderiv1.contDiffAt (x := x)).differentiableAt
      (by decide)).hasDerivAt
  exact ladder_commutator_pointwise_of_hasDerivAt _ _ _ x hf1 hf2

/-- Annihilation operator as an `OperatorWithDomain` record (MF10
`PhyslibExt.Quantum.FiniteState` pattern; domain is the Schwartz
carrier). Its values are not proved to lie in the Schwartz carrier, so it
does not compose with `creation`; the ladder identity of this module is stated
for `annFun`/`creFun` (`ladder_commutator_pointwise_schwartz`). -/
noncomputable def annihilation : Quantum.FiniteState.OperatorWithDomain where
  domain := SchwartzCarrier
  op f x := annFun (f : ℝ → ℂ) x

/-- Creation operator as an `OperatorWithDomain` record (same MF10
pattern and the same caveat as `annihilation`). -/
noncomputable def creation : Quantum.FiniteState.OperatorWithDomain where
  domain := SchwartzCarrier
  op f x := creFun (f : ℝ → ℂ) x

/-- Box position mean `⟨x⟩ = L / 2`, via `x * sin^2 = (x/L) - (x/L) cos 2θ`
and interval integrals (the `x * cos` integral vanishes by FTC). -/
lemma box_moment_x (n : ℕ) (L : ℝ) (hn : 1 ≤ n) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, x * (boxFunction n L x) ^ 2 = L / 2 := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have h2L : (0:ℝ) ≤ 2 / L := div_nonneg (by norm_num) (le_of_lt hL)
  have hA2 : Real.sqrt (2 / L) ^ 2 = 2 / L := Real.sq_sqrt h2L
  have hpt : ∀ x : ℝ, x * (boxFunction n L x) ^ 2
      = (x / L) - (x / L) * Real.cos (2 * (↑n * Real.pi * x / L)) := by
    intro x
    have hpt0 : boxFunction n L x
        = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L) := rfl
    have h1 := Real.cos_two_mul (↑n * Real.pi * x / L)
    have h2 := Real.sin_sq_add_cos_sq (↑n * Real.pi * x / L)
    have hsq : (Real.sin (↑n * Real.pi * x / L)) ^ 2
        = (1 - Real.cos (2 * (↑n * Real.pi * x / L))) / 2 := by linarith
    rw [hpt0]
    have hmid : x * (Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L)) ^ 2
        = x * ((Real.sqrt (2 / L) ^ 2)
          * ((Real.sin (↑n * Real.pi * x / L)) ^ 2)) := by ring
    rw [hmid, hA2, hsq]
    ring
  have hfun : (fun x : ℝ => x * (boxFunction n L x) ^ 2)
      = (fun x : ℝ => (x / L)
        - (x / L) * Real.cos (2 * (↑n * Real.pi * x / L))) := by
    funext x
    exact hpt x
  rw [hfun]
  have hC : IntervalIntegrable (fun x : ℝ => x / L)
      MeasureTheory.volume 0 L :=
    (continuous_id.div_const L).intervalIntegrable 0 L
  have hK : IntervalIntegrable
      (fun x : ℝ => (x / L) * Real.cos (2 * (↑n * Real.pi * x / L)))
      MeasureTheory.volume 0 L := by
    have hcK : Continuous
        (fun x : ℝ => (x / L) * Real.cos (2 * (↑n * Real.pi * x / L))) := by
      fun_prop
    exact hcK.intervalIntegrable 0 L
  have hsub : (∫ x in (0:ℝ)..L, (x / L)
        - (x / L) * Real.cos (2 * (↑n * Real.pi * x / L)))
      = (∫ x in (0:ℝ)..L, x / L)
        - ∫ x in (0:ℝ)..L, (x / L)
          * Real.cos (2 * (↑n * Real.pi * x / L)) :=
    intervalIntegral.integral_sub hC hK
  have eC : (∫ x in (0:ℝ)..L, x / L) = L / 2 := by
    have hfunC : (fun x : ℝ => x / L) = (fun x : ℝ => (1 / L) * x) := by
      funext x
      ring
    rw [hfunC]
    have hFx : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      intro x
      have h0 := (hasDerivAt_pow 2 x).div_const 2
      convert h0 using 1
      all_goals try funext y
      all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one,
        Nat.cast_ofNat, Pi.mul_apply, id_eq]
      all_goals try field_simp
      all_goals try ring
    have hintX : IntervalIntegrable (fun x : ℝ => x)
        MeasureTheory.volume 0 L :=
      continuous_id.intervalIntegrable 0 L
    have hFTCx : (∫ x in (0:ℝ)..L, x) = L ^ 2 / 2 - 0 ^ 2 / 2 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFx x) hintX
    have eX : (∫ x in (0:ℝ)..L, x) = L ^ 2 / 2 := by
      rw [hFTCx]
      ring
    have hcm : (∫ x in (0:ℝ)..L, (1 / L) * x)
        = (1 / L) * ∫ x in (0:ℝ)..L, x :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm, eX]
    field_simp
    try ring
  have eK : (∫ x in (0:ℝ)..L, (x / L)
      * Real.cos (2 * (↑n * Real.pi * x / L))) = 0 := by
    have hfunK : (fun x : ℝ => (x / L)
          * Real.cos (2 * (↑n * Real.pi * x / L)))
        = (fun x : ℝ => (1 / L)
          * (x * Real.cos (2 * (↑n * Real.pi * x / L)))) := by
      funext x
      ring
    rw [hfunK]
    have hcm : (∫ x in (0:ℝ)..L, (1 / L)
          * (x * Real.cos (2 * (↑n * Real.pi * x / L))))
        = (1 / L) * ∫ x in (0:ℝ)..L,
          (x * Real.cos (2 * (↑n * Real.pi * x / L))) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm]
    have hG : ∀ x : ℝ, HasDerivAt
        (fun x : ℝ => x * Real.sin (2 * (↑n * Real.pi * x / L))
            / ((2 * ↑n) * Real.pi / L)
          + Real.cos (2 * (↑n * Real.pi * x / L))
            / (((2 * ↑n) * Real.pi / L) ^ 2))
        (x * Real.cos (2 * (↑n * Real.pi * x / L))) x := by
      intro x
      have hn0 : 0 < n := by omega
      have hn' : (↑n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn0
      have hk : (((2 * ↑n) * Real.pi / L)) ≠ 0 :=
        div_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) hn') Real.pi_ne_zero) hL'
      have hk2 : ((((2 * ↑n) * Real.pi / L)) ^ 2) ≠ 0 := pow_ne_zero 2 hk
      have hsin2 : HasDerivAt
          (fun x : ℝ => Real.sin (2 * (↑n * Real.pi * x / L)))
          (Real.cos (2 * (↑n * Real.pi * x / L))
            * (2 * ((↑n * Real.pi) / L))) x := by
        have h0 :=
          ((hasDerivAt_affine (↑n * Real.pi) L x).const_mul 2).sin
        convert h0 using 1
        all_goals try funext y
        all_goals try simp only [Pi.mul_apply, id_eq]
        all_goals try field_simp
        all_goals try ring
      have hcos2 : HasDerivAt
          (fun x : ℝ => Real.cos (2 * (↑n * Real.pi * x / L)))
          (-Real.sin (2 * (↑n * Real.pi * x / L))
            * (2 * ((↑n * Real.pi) / L))) x := by
        have h0 :=
          ((hasDerivAt_affine (↑n * Real.pi) L x).const_mul 2).cos
        convert h0 using 1
        all_goals try funext y
        all_goals try simp only [Pi.mul_apply, id_eq]
        all_goals try field_simp
        all_goals try ring
      have h0 : HasDerivAt
          (fun x : ℝ => x * Real.sin (2 * (↑n * Real.pi * x / L))
              / ((2 * ↑n) * Real.pi / L)
            + Real.cos (2 * (↑n * Real.pi * x / L))
              / (((2 * ↑n) * Real.pi / L) ^ 2))
          (x * Real.cos (2 * (↑n * Real.pi * x / L))) x := by
        have h00 := (((hasDerivAt_id x).mul hsin2).div_const
          ((2 * ↑n) * Real.pi / L)).add
          (hcos2.div_const (((2 * ↑n) * Real.pi / L) ^ 2))
        convert h00 using 1
        all_goals try funext y
        all_goals try simp only [Pi.mul_apply, Pi.add_apply, id_eq, zero_mul, mul_zero,
          mul_one, one_mul, zero_add, add_zero, sub_zero, zero_sub, sub_self,
          neg_zero]
        all_goals try field_simp
        all_goals try ring
      exact h0
    have hintG : IntervalIntegrable
        (fun x : ℝ => x * Real.cos (2 * (↑n * Real.pi * x / L)))
        MeasureTheory.volume 0 L := by
      have hcG : Continuous
          (fun x : ℝ => x * Real.cos (2 * (↑n * Real.pi * x / L))) := by
        fun_prop
      exact hcG.intervalIntegrable 0 L
    have hFTC : (∫ x in (0:ℝ)..L,
          (x * Real.cos (2 * (↑n * Real.pi * x / L))))
        = (L * Real.sin (2 * (↑n * Real.pi * L / L))
            / ((2 * ↑n) * Real.pi / L)
          + Real.cos (2 * (↑n * Real.pi * L / L))
            / (((2 * ↑n) * Real.pi / L) ^ 2))
          - (0 * Real.sin (2 * (↑n * Real.pi * 0 / L))
            / ((2 * ↑n) * Real.pi / L)
          + Real.cos (2 * (↑n * Real.pi * 0 / L))
            / (((2 * ↑n) * Real.pi / L) ^ 2)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) hintG
    have eL : 2 * (↑n * Real.pi * L / L) = ↑(2 * n) * Real.pi := by
      push_cast
      field_simp
      try ring
    have eL2 : 2 * (↑n * Real.pi * L / L) = 2 * (↑n * Real.pi) := by
      field_simp
      try ring
    have hcosL : Real.cos (2 * (↑n * Real.pi * L / L)) = 1 := by
      rw [eL2]
      have h1 := Real.cos_two_mul (↑n * Real.pi)
      have h2 := Real.sin_sq_add_cos_sq (↑n * Real.pi)
      have h3 := Real.sin_nat_mul_pi n
      have h4 : Real.sin (↑n * Real.pi) ^ 2 = 0 := by
        rw [h3]
        norm_num
      linarith
    have e0 : 2 * (↑n * Real.pi * 0 / L) = 0 := by ring
    rw [hFTC, hcosL, eL, Real.sin_nat_mul_pi (2 * n), e0, Real.sin_zero,
      Real.cos_zero]
    ring
  rw [hsub, eC, eK, sub_zero]

/-- Box position second moment `⟨x^2⟩ = L^2 (1/3 - 1/(2n^2π^2))`, via
`x^2 * sin^2 = (x^2/L) - (x^2/L) cos 2θ` and interval integrals. -/
lemma box_moment_x2 (n : ℕ) (L : ℝ) (hn : 1 ≤ n) (hL : 0 < L) :
    ∫ x in (0:ℝ)..L, x ^ 2 * (boxFunction n L x) ^ 2
      = L ^ 2 * (1 / 3 - 1 / (2 * ↑n ^ 2 * Real.pi ^ 2)) := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have h2L : (0:ℝ) ≤ 2 / L := div_nonneg (by norm_num) (le_of_lt hL)
  have hA2 : Real.sqrt (2 / L) ^ 2 = 2 / L := Real.sq_sqrt h2L
  have hpt : ∀ x : ℝ, x ^ 2 * (boxFunction n L x) ^ 2
      = (x ^ 2 / L) - (x ^ 2 / L) * Real.cos (2 * (↑n * Real.pi * x / L)) := by
    intro x
    have hpt0 : boxFunction n L x
        = Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L) := rfl
    have h1 := Real.cos_two_mul (↑n * Real.pi * x / L)
    have h2 := Real.sin_sq_add_cos_sq (↑n * Real.pi * x / L)
    have hsq : (Real.sin (↑n * Real.pi * x / L)) ^ 2
        = (1 - Real.cos (2 * (↑n * Real.pi * x / L))) / 2 := by linarith
    rw [hpt0]
    have hmid : x ^ 2
          * (Real.sqrt (2 / L) * Real.sin (↑n * Real.pi * x / L)) ^ 2
        = x ^ 2 * ((Real.sqrt (2 / L) ^ 2)
          * ((Real.sin (↑n * Real.pi * x / L)) ^ 2)) := by ring
    rw [hmid, hA2, hsq]
    ring
  have hfun : (fun x : ℝ => x ^ 2 * (boxFunction n L x) ^ 2)
      = (fun x : ℝ => (x ^ 2 / L)
        - (x ^ 2 / L) * Real.cos (2 * (↑n * Real.pi * x / L))) := by
    funext x
    exact hpt x
  rw [hfun]
  have hC : IntervalIntegrable (fun x : ℝ => x ^ 2 / L)
      MeasureTheory.volume 0 L := by
    have hcont : Continuous (fun x : ℝ => x ^ 2 / L) := by
      fun_prop
    exact hcont.intervalIntegrable 0 L
  have hK : IntervalIntegrable
      (fun x : ℝ => (x ^ 2 / L) * Real.cos (2 * (↑n * Real.pi * x / L)))
      MeasureTheory.volume 0 L := by
    have hcK : Continuous
        (fun x : ℝ => (x ^ 2 / L) * Real.cos (2 * (↑n * Real.pi * x / L))) := by
      fun_prop
    exact hcK.intervalIntegrable 0 L
  have hsub : (∫ x in (0:ℝ)..L, (x ^ 2 / L)
        - (x ^ 2 / L) * Real.cos (2 * (↑n * Real.pi * x / L)))
      = (∫ x in (0:ℝ)..L, x ^ 2 / L)
        - ∫ x in (0:ℝ)..L, (x ^ 2 / L)
          * Real.cos (2 * (↑n * Real.pi * x / L)) :=
    intervalIntegral.integral_sub hC hK
  have eC : (∫ x in (0:ℝ)..L, x ^ 2 / L) = L ^ 2 / 3 := by
    have hfunC : (fun x : ℝ => x ^ 2 / L) = (fun x : ℝ => (1 / L) * x ^ 2) := by
      funext x
      ring
    rw [hfunC]
    have hFx : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 3 / 3) (x ^ 2) x := by
      intro x
      have h0 := (hasDerivAt_pow 3 x).div_const 3
      convert h0 using 1
      all_goals try funext y
      all_goals try simp only [show (3:ℕ) - 1 = 2 from by decide, Nat.cast_ofNat,
        Pi.mul_apply, id_eq]
      all_goals try field_simp
      all_goals try ring
    have hintX : IntervalIntegrable (fun x : ℝ => x ^ 2)
        MeasureTheory.volume 0 L := by
      have hcX : Continuous (fun x : ℝ => x ^ 2) := by
        fun_prop
      exact hcX.intervalIntegrable 0 L
    have hFTCx : (∫ x in (0:ℝ)..L, x ^ 2) = L ^ 3 / 3 - 0 ^ 3 / 3 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFx x) hintX
    have eX : (∫ x in (0:ℝ)..L, x ^ 2) = L ^ 3 / 3 := by
      rw [hFTCx]
      ring
    have hcm : (∫ x in (0:ℝ)..L, (1 / L) * x ^ 2)
        = (1 / L) * ∫ x in (0:ℝ)..L, x ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm, eX]
    field_simp
    try ring
  have eK : (∫ x in (0:ℝ)..L, (x ^ 2 / L)
      * Real.cos (2 * (↑n * Real.pi * x / L)))
      = (1 / L) * (2 * L / (((2 * ↑n) * Real.pi / L) ^ 2)) := by
    have hfunK : (fun x : ℝ => (x ^ 2 / L)
          * Real.cos (2 * (↑n * Real.pi * x / L)))
        = (fun x : ℝ => (1 / L)
          * (x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L)))) := by
      funext x
      ring
    rw [hfunK]
    have hcm : (∫ x in (0:ℝ)..L, (1 / L)
          * (x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L))))
        = (1 / L) * ∫ x in (0:ℝ)..L,
          (x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L))) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcm]
    have hH : ∀ x : ℝ, HasDerivAt
        (fun x : ℝ => x ^ 2 * Real.sin (2 * (↑n * Real.pi * x / L))
            / ((2 * ↑n) * Real.pi / L)
          + 2 * x * Real.cos (2 * (↑n * Real.pi * x / L))
            / (((2 * ↑n) * Real.pi / L) ^ 2)
          - 2 * Real.sin (2 * (↑n * Real.pi * x / L))
            / (((2 * ↑n) * Real.pi / L) ^ 3))
        (x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L))) x := by
      intro x
      have hn0 : 0 < n := by omega
      have hn' : (↑n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn0
      have hk : (((2 * ↑n) * Real.pi / L)) ≠ 0 :=
        div_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) hn') Real.pi_ne_zero) hL'
      have hk2 : ((((2 * ↑n) * Real.pi / L)) ^ 2) ≠ 0 := pow_ne_zero 2 hk
      have hk3 : ((((2 * ↑n) * Real.pi / L)) ^ 3) ≠ 0 := pow_ne_zero 3 hk
      have hsin2 : HasDerivAt
          (fun x : ℝ => Real.sin (2 * (↑n * Real.pi * x / L)))
          (Real.cos (2 * (↑n * Real.pi * x / L))
            * (2 * ((↑n * Real.pi) / L))) x := by
        have h0 :=
          ((hasDerivAt_affine (↑n * Real.pi) L x).const_mul 2).sin
        convert h0 using 1
        all_goals try funext y
        all_goals try simp only [Pi.mul_apply, id_eq]
        all_goals try field_simp
        all_goals try ring
      have hcos2 : HasDerivAt
          (fun x : ℝ => Real.cos (2 * (↑n * Real.pi * x / L)))
          (-Real.sin (2 * (↑n * Real.pi * x / L))
            * (2 * ((↑n * Real.pi) / L))) x := by
        have h0 :=
          ((hasDerivAt_affine (↑n * Real.pi) L x).const_mul 2).cos
        convert h0 using 1
        all_goals try funext y
        all_goals try simp only [Pi.mul_apply, id_eq]
        all_goals try field_simp
        all_goals try ring
      have h0 : HasDerivAt
          (fun x : ℝ => x ^ 2 * Real.sin (2 * (↑n * Real.pi * x / L))
              / ((2 * ↑n) * Real.pi / L)
            + 2 * x * Real.cos (2 * (↑n * Real.pi * x / L))
              / (((2 * ↑n) * Real.pi / L) ^ 2)
            - 2 * Real.sin (2 * (↑n * Real.pi * x / L))
              / (((2 * ↑n) * Real.pi / L) ^ 3))
          (x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L))) x := by
        have h00 := ((((hasDerivAt_pow 2 x).mul hsin2).div_const
          ((2 * ↑n) * Real.pi / L)).add
          ((((hasDerivAt_id x).const_mul 2).mul hcos2).div_const
            (((2 * ↑n) * Real.pi / L) ^ 2))).sub
          ((hsin2.const_mul 2).div_const (((2 * ↑n) * Real.pi / L) ^ 3))
        convert h00 using 1
        all_goals try funext y
        all_goals try simp only [show (2:ℕ) - 1 = 1 from by decide, pow_one,
          Nat.cast_ofNat, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq,
          zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero, sub_zero,
          zero_sub, sub_self, neg_zero]
        all_goals try field_simp
        all_goals try ring
      exact h0
    have hintH : IntervalIntegrable
        (fun x : ℝ => x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L)))
        MeasureTheory.volume 0 L := by
      have hcH : Continuous
          (fun x : ℝ => x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L))) := by
        fun_prop
      exact hcH.intervalIntegrable 0 L
    have hFTC : (∫ x in (0:ℝ)..L,
          (x ^ 2 * Real.cos (2 * (↑n * Real.pi * x / L))))
        = (L ^ 2 * Real.sin (2 * (↑n * Real.pi * L / L))
            / ((2 * ↑n) * Real.pi / L)
          + 2 * L * Real.cos (2 * (↑n * Real.pi * L / L))
            / (((2 * ↑n) * Real.pi / L) ^ 2)
          - 2 * Real.sin (2 * (↑n * Real.pi * L / L))
            / (((2 * ↑n) * Real.pi / L) ^ 3))
          - (0 ^ 2 * Real.sin (2 * (↑n * Real.pi * 0 / L))
            / ((2 * ↑n) * Real.pi / L)
          + 2 * 0 * Real.cos (2 * (↑n * Real.pi * 0 / L))
            / (((2 * ↑n) * Real.pi / L) ^ 2)
          - 2 * Real.sin (2 * (↑n * Real.pi * 0 / L))
            / (((2 * ↑n) * Real.pi / L) ^ 3)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hH x) hintH
    have eL : 2 * (↑n * Real.pi * L / L) = ↑(2 * n) * Real.pi := by
      push_cast
      field_simp
      try ring
    have eL2 : 2 * (↑n * Real.pi * L / L) = 2 * (↑n * Real.pi) := by
      field_simp
      try ring
    have hcosL : Real.cos (2 * (↑n * Real.pi * L / L)) = 1 := by
      rw [eL2]
      have h1 := Real.cos_two_mul (↑n * Real.pi)
      have h2 := Real.sin_sq_add_cos_sq (↑n * Real.pi)
      have h3 := Real.sin_nat_mul_pi n
      have h4 : Real.sin (↑n * Real.pi) ^ 2 = 0 := by
        rw [h3]
        norm_num
      linarith
    have e0 : 2 * (↑n * Real.pi * 0 / L) = 0 := by ring
    rw [hFTC, hcosL, eL, Real.sin_nat_mul_pi (2 * n), e0, Real.sin_zero,
      Real.cos_zero]
    ring
  rw [hsub, eC, eK]
  field_simp
  try ring

/-! ## Section D: free-electron polyene model. -/

/-- MODEL (free-electron + box): box length for `k` double bonds,
`L = (2k+1) * a` with `a > 0` mean bond length. Model input, not a
measurement. -/
noncomputable def polyeneLength (k : ℕ) (a : ℝ) : ℝ := (2 * ↑k + 1) * a

/-- MODEL: HOMO-LUMO gap `ΔE = E(k+1) - E(k)` from `boxEnergy`
(HOMO `n = k`, LUMO `n = k + 1` for `N = 2k` π-electrons). -/
noncomputable def polyeneGap (k : ℕ) (L m ħ : ℝ) : ℝ :=
  boxEnergy (k + 1) L m ħ - boxEnergy k L m ħ

/-- MODEL: absorption wavelength `h * c / ΔE` with `h = 2πħ`
(`planckH`) and symbolic `c > 0`. -/
noncomputable def polyeneWavelength (k : ℕ) (L m ħ c : ℝ) : ℝ :=
  planckH ħ * c / polyeneGap k L m ħ

/-- MODEL estimate (free-electron + box, not a measurement or a theorem
about real polyenes): closed form of the model wavelength,
`wavelength = 8 * m * c * L^2 / (h * (2k+1))`, for `k ≥ 1` double
bonds with `L = (2k+1) * a`. -/
lemma polyene_wavelength_closed_form (k : ℕ) (a m ħ c : ℝ) (hk : 1 ≤ k)
    (ha : 0 < a) (hm : 0 < m) (hħ : 0 < ħ) (hc : 0 < c) :
    polyeneWavelength k (polyeneLength k a) m ħ c
      = 8 * m * c * (polyeneLength k a) ^ 2
        / (planckH ħ * (2 * ↑k + 1)) := by
  have hk0 : (0:ℝ) < ↑k := by exact_mod_cast lt_of_lt_of_le (by norm_num) hk
  have h2k1 : (0:ℝ) < 2 * ↑k + 1 := by linarith
  have hL : (0:ℝ) < polyeneLength k a := by
    unfold polyeneLength
    exact mul_pos h2k1 ha
  have h8 : ((8:ℝ) * m * (polyeneLength k a) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hm))
      (pow_ne_zero 2 (ne_of_gt hL))
  have hH : ((2 * Real.pi * ħ):ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ne_of_gt hħ)
  have hH2 : (((2 * Real.pi * ħ) ^ 2):ℝ) ≠ 0 := pow_ne_zero 2 hH
  have hgap_eq : polyeneGap k (polyeneLength k a) m ħ
      = ((2 * ↑k + 1) * (2 * Real.pi * ħ) ^ 2)
        / (8 * m * (polyeneLength k a) ^ 2) := by
    unfold polyeneGap boxEnergy
    push_cast
    ring
  have hgap : polyeneGap k (polyeneLength k a) m ħ ≠ 0 := by
    rw [hgap_eq]
    exact div_ne_zero (mul_ne_zero (ne_of_gt h2k1) hH2) h8
  have hHk : ((2 * Real.pi * ħ) * (2 * ↑k + 1)) ≠ 0 :=
    mul_ne_zero hH (ne_of_gt h2k1)
  have hnum : (((2 * ↑k + 1) * (2 * Real.pi * ħ) ^ 2):ℝ) ≠ 0 :=
    mul_ne_zero (ne_of_gt h2k1) hH2
  have hHπ : planckH ħ = 2 * Real.pi * ħ := rfl
  unfold polyeneWavelength
  rw [hgap_eq, hHπ]
  field_simp
  try ring

/-! ## Section E: explicit deferrals (visible; never silent).

* Completeness of the box eigenfunctions in `L^2(0, L)` and
  self-adjointness of the box Hamiltonian on `H^2 ∩ H^1_0`: DEFERRED
  (allowed by the contract). Nothing in this module proves or assumes
  either statement. Sobolev regularity is NOT developed here, and the
  Sobolev domain `H²(0, L) ∩ H¹₀(0, L)` is not modeled: `BoxC2Dirichlet` is
  only a carrier of smooth real functions.
* General-`v` oscillator eigen-equation: Physlib's proved result, cited
  in prose only (see the module header).
* General-`v` oscillator orthonormality: Physlib's proved
  `eigenfunction_orthonormal`, for Physlib's `HarmonicOscillator` and its
  constants, cited in prose only (see the module header); not restated
  here.
* Oscillator orthonormality for `(v, w) ∈ {0,1,2}^2`: PROVED
  (`osc_orthonormality_00/01/10/02/20/11/12/21/22`) by explicit Gaussian
  moments (odd vanishing by whole-line negation symmetry; even moments
  by integration by parts from the base Gaussian integral). General-`v`
  orthonormality (beyond `{0,1,2}`) is not restated here (see the Physlib
  citation in the module header).
-/

end Chemistry.Quantum.OneDimensionalModels
