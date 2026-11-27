/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.RootsOfUnity.Complex
import MathlibExt.Analysis.Complex.ArgumentPrincipleCurve
import MathlibExt.Analysis.Complex.CasoratiWeierstrass
import MathlibExt.Analysis.Complex.MittagLefflerPolynomial
import MathlibExt.Analysis.Complex.NormalFamilies
import MathlibExt.Analysis.Complex.RoucheCurve
import MathlibExt.Analysis.LaplaceTransform.ExponentialBound
import MathlibExt.Analysis.LaplaceTransform.NewmanTauberian
import MathlibExt.NumberTheory.LSeries.PrimeLog

/-!
Canonical APIs for the archived `v1/Atlas/ComplexVariables` targets that Mathlib or `MathlibExt`
already proves. Each example states the library form of a target, numbered by its zero-based
ordinal in `v1/Atlas/ComplexVariables/targets.yaml`. These are canonical-use checks, recording
where and in which form the library proves each target, not a new verification of the printed
notes.

Targets 22 (the argument principle for a simple closed curve), 23 (Rouché's theorem for a simple
closed curve) and 37 (Newman's analytic theorem) replace archived proofs that rest on `sorry`.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter Topology
open scoped Real

-- Target 0: `b ^ x = exp (x log b)` (the book takes `b > 1`; Mathlib needs only `b > 0`).
example {b : ℝ} (hb : 1 < b) (x : ℝ) : b ^ x = Real.exp (x * Real.log b) := by
  rw [Real.rpow_def_of_pos (by linarith), mul_comm]

-- Target 1: `b ^ (x + y) = b ^ x b ^ y` for every `b > 0`.
example {b : ℝ} (hb : 0 < b) (x y : ℝ) : b ^ (x + y) = b ^ x * b ^ y :=
  Real.rpow_add hb x y

-- Target 2: `e ^ (z + w) = e ^ z e ^ w`.
example (z w : ℂ) : exp (z + w) = exp z * exp w := exp_add z w

-- Target 3: the `n`-th roots of unity are the powers of `e^{2πi/n}`.
example (n : ℕ) [NeZero n] (z : ℂˣ) :
    z ∈ rootsOfUnity n ℂ ↔ ∃ i < n, exp (2 * π * I * (i / n)) = z :=
  Complex.mem_rootsOfUnity n z

-- Target 5: Gauss–Lucas.
example (P : Polynomial ℂ) (h : 0 < P.degree) :
    P.derivative.rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ) :=
  Polynomial.rootSet_derivative_subset_convexHull_rootSet h

-- Target 6: the convex hull of finitely many points is the set of their convex combinations.
example (s : Finset ℂ) (x : ℂ) :
    x ∈ convexHull ℝ (s : Set ℂ) ↔
      ∃ w : ℂ → ℝ, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x :=
  Finset.mem_convexHull'

-- Target 12: Casorati–Weierstrass.
example {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r \ {c})) (hess : ¬ MeromorphicAt f c) :
    Dense (f '' (Metric.ball c r \ {c})) :=
  MathlibExt.Analysis.Complex.CasoratiWeierstrass.casoratiWeierstrass hr hf hess

-- Target 22: the argument principle for a simple closed curve. `γ` is a closed piecewise `C¹`
-- path, injective on `[0, 1)`, positively oriented (winding number `1` at every point inside it),
-- with `γ` and its inside in `Ω` and no zero or pole of `f` on `γ`. `N - P` is the sum over the
-- inside of `γ` of the positive minus the negative part of the divisor of `f`, a finite sum.
example {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : MeromorphicOn f Ω) {x : ℂ}
    {γ : Path x x} (hγ : γ.IsPiecewiseC1) (hγs : Set.InjOn γ (Set.Iio 1))
    (hγ_pos : ∀ w ∈ (Set.range γ).inside, windingNumber γ w = 1) (hγΩ : Set.range γ ⊆ Ω)
    (hinsΩ : (Set.range γ).inside ⊆ Ω) (hγf : ∀ z ∈ Set.range γ, meromorphicOrderAt f z = 0) :
    ((MeromorphicOn.divisor f Ω).support ∩ (Set.range γ).inside).Finite ∧
      (2 * π * I)⁻¹ * ∫ᶜ z in γ, logDeriv f z • ContinuousLinearMap.id ℂ ℂ =
        (((∑ᶠ z ∈ (Set.range γ).inside, (MeromorphicOn.divisor f Ω)⁺ z) -
          ∑ᶠ z ∈ (Set.range γ).inside, (MeromorphicOn.divisor f Ω)⁻ z : ℤ) : ℂ) :=
  MeromorphicOn.argument_principle hΩ hf hγ hγs hγ_pos hγΩ hinsΩ hγf

-- Target 23: Rouché's theorem for a simple closed curve `γ : Circle → ℂ` whose interior
-- `Set.inside (range γ)` lies in the region `Ω`. If `‖f - g‖ < ‖f‖` on `γ`, then `f` and `g` have
-- finitely many zeros inside `γ`, and the same number of them, counted with multiplicity.
example {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsConnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω) {γ : Circle → ℂ}
    (hγc : Continuous γ) (hγ : Function.Injective γ) (hγΩ : Set.range γ ⊆ Ω)
    (hinside : (Set.range γ).inside ⊆ Ω) (hfg : ∀ t, ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖) :
    {z ∈ (Set.range γ).inside | f z = 0}.Finite ∧ {z ∈ (Set.range γ).inside | g z = 0}.Finite ∧
      ∑ᶠ z ∈ (Set.range γ).inside, analyticOrderNatAt f z =
        ∑ᶠ z ∈ (Set.range γ).inside, analyticOrderNatAt g z :=
  Complex.rouche hΩ hΩc hf hg hγc hγ hγΩ hinside hfg

-- Target 24: on an open set, harmonic in the sense of the notes (`C²` with
-- `∂²u/∂x² + ∂²u/∂y² = 0`) is Mathlib's `HarmonicOnNhd`, whose Laplacian on `ℂ` is the sum of the
-- second derivatives along `1` and `I`.
example {u : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    InnerProductSpace.HarmonicOnNhd u Ω ↔ ContDiffOn ℝ 2 u Ω ∧
      ∀ z ∈ Ω, iteratedFDeriv ℝ 2 u z ![1, 1] + iteratedFDeriv ℝ 2 u z ![I, I] = 0 := by
  refine ⟨fun hu => ⟨hu.contDiffOn, fun z hz => ?_⟩, fun ⟨hC, hΔ⟩ z hz =>
    ⟨hC.contDiffAt (hΩ.mem_nhds hz), ?_⟩⟩
  · have := (hu z hz).2.self_of_nhds
    rwa [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at this
  · filter_upwards [hΩ.mem_nhds hz] with w hw
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    exact hΔ w hw

-- Target 26: the mean value property of harmonic functions on a closed disc.
example {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |R|)) :
    Real.circleAverage u c R = u c :=
  hu.circleAverage_eq

-- Target 29: Mittag-Leffler's theorem. For distinct `b ν → ∞` and polynomials `P ν` without
-- constant term, some meromorphic `f` has singular part `P ν (1 / (z - b ν))` at each `b ν` and no
-- other poles, and for suitable polynomials `p ν` every such `f` is
-- `g + ∑ ν, (P ν (1 / (z - b ν)) - p ν z)` off the poles, with `g` entire.
example {b : ℕ → ℂ} (hb_inj : Function.Injective b) (hb : Tendsto (fun ν => ‖b ν‖) atTop atTop)
    (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).coeff 0 = 0) :
    (∃ f : ℂ → ℂ, Meromorphic f ∧ (∀ z ∉ Set.range b, AnalyticAt ℂ f z) ∧
      ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
        ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z) ∧
    ∃ p : ℕ → Polynomial ℂ, ∀ f : ℂ → ℂ,
      (Meromorphic f ∧ (∀ z ∉ Set.range b, AnalyticAt ℂ f z) ∧
        ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
          ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z) ↔
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        ∀ z ∉ Set.range b, HasSum (fun ν => (P ν).eval (z - b ν)⁻¹ - (p ν).eval z) (f z - g z) :=
  Complex.mittag_leffler_of_coeff_zero_eq_zero hb_inj hb P hP

-- Target 31: the beta integral.
example (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = Gamma u * Gamma v / Gamma (u + v) :=
  Complex.betaIntegral_eq_Gamma_mul_div u v hu hv

-- Target 32: Montel's theorem.
example {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ) (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hB : MathlibExt.Analysis.Complex.NormalFamilies.IsLocallyUniformlyBoundedOn U F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop U :=
  MathlibExt.Analysis.Complex.NormalFamilies.montel hU F hF hB

-- Target 33: `1 / ζ(s) = ∏_p (1 - p^{-s})` for `Re s > 1`.
example {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 - (p : ℂ) ^ (-s)) (riemannZeta s)⁻¹ := by
  simpa only [inv_inv] using
    (riemannZeta_eulerProduct_hasProd hs).inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)

-- Target 34: `ζ(s) - 1/(s - 1)` extends holomorphically (here to all of `ℂ`).
example {s : ℂ} (hs : s ≠ 1) : riemannZeta s - (s - 1)⁻¹ = riemannZeta₀ s := by
  rw [riemannZeta_eq_inv_sub_add hs]; ring

example : Differentiable ℂ riemannZeta₀ := differentiable_riemannZeta₀

-- Target 35: `θ(x) = O(x)`.
example {x : ℝ} (hx : 0 ≤ x) : Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

-- Target 36: `ζ(s) ≠ 0` for `Re s ≥ 1`, and `Φ(s) - 1/(s - 1)` (with `Φ(s) = ∑_p log p / p ^ s`)
-- extends to a function analytic at every point of `Re s ≥ 1`; both parts in one statement. The
-- notes' `ζ` has a pole at `s = 1`, where Mathlib's `riemannZeta 1` is a junk value, so the
-- nonvanishing clause excludes `s = 1`.
example :
    (∀ s : ℂ, 1 ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
        Set.EqOn F (fun s => Nat.Primes.logDirichletSeries s - 1 / (s - 1)) {s | 1 < s.re} :=
  ⟨fun _ hs _ => riemannZeta_ne_zero_of_one_le_re hs, Nat.Primes.logDirichletContinuation,
    Nat.Primes.logDirichletContinuation_analyticOn, Nat.Primes.logDirichletContinuation_agree⟩

-- Target 37: Newman's analytic theorem in the book's form. If `f` is bounded and locally
-- integrable on `[0, ∞)` and its Laplace transform `g z = ∫₀^∞ e^{-zt} f t dt` (`Re z > 0`) extends
-- holomorphically to `Re z ≥ 0`, then `∫₀^T f → g 0`.
example {f : ℝ → ℂ} {g : ℂ → ℂ} (hf_bdd : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hf_loc : MeasureTheory.LocallyIntegrableOn f (Set.Ici 0))
    (hg_laplace : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-z * t) * f t)
    (hg : AnalyticOnNhd ℂ g {z | 0 ≤ z.re}) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (g 0)) := by
  obtain ⟨B, hB⟩ := hf_bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  have hmeas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hf_loc.aestronglyMeasurable.mono_set Set.Ioi_subset_Ici_self
  refine newman_tauberian f B hmeas hB0 hB g hg fun z hz => ⟨?_, ?_⟩
  · refine laplaceConvergent_of_norm_le_exp f 0 B hmeas hB0 (fun t ht => ?_) hz
    simpa using hB t ht
  · simp only [laplace, smul_eq_mul, hg_laplace z hz]
