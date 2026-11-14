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
import MathlibExt.Analysis.Complex.ArgumentPrinciple
import MathlibExt.Analysis.Complex.CasoratiWeierstrass
import MathlibExt.Analysis.Complex.MittagLeffler
import MathlibExt.Analysis.Complex.NormalFamilies
import MathlibExt.Analysis.Complex.Rouche
import MathlibExt.Analysis.LaplaceTransform.ExponentialBound
import MathlibExt.Analysis.LaplaceTransform.NewmanTauberian
import MathlibExt.NumberTheory.LSeries.PrimeLog

/-!
Canonical APIs for the archived `v1/Atlas/ComplexVariables` targets that Mathlib or `MathlibExt`
already proves. Each example states the library form of a target, numbered by its zero-based
ordinal in `v1/Atlas/ComplexVariables/targets.yaml`. Targets 22, 23 and 37 replace archived
proofs that rest on `sorry`; target 29 adds the uniqueness clause of Mittag-Leffler, which the
library states only as existence. These are canonical-use checks, not verification against the
printed textbook.
-/

set_option autoImplicit false
noncomputable section

open Complex Filter Topology
open scoped Real

-- Target 0: `b ^ x = exp (x log b)` (the book takes `b > 1`; Mathlib needs only `b > 0`).
example {b : ℝ} (hb : 1 < b) (x : ℝ) : b ^ x = Real.exp (x * Real.log b) := by
  rw [Real.rpow_def_of_pos (by linarith), mul_comm]

-- Target 1: `b ^ (x + y) = b ^ x b ^ y`.
example {b : ℝ} (hb : 1 < b) (x y : ℝ) : b ^ (x + y) = b ^ x * b ^ y :=
  Real.rpow_add (by linarith) x y

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

-- Target 22: the argument principle on a disc.
example {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : MeromorphicOn f (Metric.closedBall c R))
    (hf_top : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ ⊤)
    (hbd : ∀ z ∈ Metric.sphere c R, MeromorphicOn.divisor f (Metric.closedBall c R) z = 0) :
    (∮ z in C(c, R), logDeriv f z) =
      2 * π * I * ↑(∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z) :=
  MathlibExt.Analysis.Complex.ArgumentPrinciple.argumentPrinciple_closedBall_general hR hf hf_top
    hbd

-- Target 23: Rouché on a disc (the book's `‖f - g‖ < ‖f‖` is `g ↦ g - f` here).
example {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hfg : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    ∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z =
      ∑ᶠ z, MeromorphicOn.divisor (fun z => f z + g z) (Metric.ball c R) z :=
  MathlibExt.Analysis.Complex.Rouche.rouche_closedBall hR hf hg hfg

-- Targets 24 and 26: harmonic functions and the mean value property.
example {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |R|)) :
    Real.circleAverage u c R = u c :=
  hu.circleAverage_eq

-- Target 29: Mittag-Leffler, existence ...
example (S : Set ℂ) (hS : IsClosed S)
    (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅)
    (coeff : ↥S → ℕ →₀ ℂ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Sᶜ ∧
      (∀ s : ↥S, AnalyticAt ℂ
        (fun z => f z - MathlibExt.Analysis.Complex.MittagLefflerWanted.principalPart s.val
          (coeff s) z) s.val) ∧
      MeromorphicOn f Set.univ :=
  MathlibExt.Analysis.Complex.MittagLefflerWanted.mittag_leffler S hS hS_discrete coeff

-- ... and uniqueness: two solutions differ by an entire function.
example (S : Set ℂ) (hS : IsClosed S) (coeff : ↥S → ℕ →₀ ℂ) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Sᶜ)
    (hf_pp : ∀ s : ↥S, AnalyticAt ℂ
      (fun z => f z - MathlibExt.Analysis.Complex.MittagLefflerWanted.principalPart s.val
        (coeff s) z) s.val)
    (hg : DifferentiableOn ℂ g Sᶜ)
    (hg_pp : ∀ s : ↥S, AnalyticAt ℂ
      (fun z => g z - MathlibExt.Analysis.Complex.MittagLefflerWanted.principalPart s.val
        (coeff s) z) s.val) :
    Differentiable ℂ (f - g) := by
  intro z
  by_cases hz : z ∈ S
  · have h := ((hf_pp ⟨z, hz⟩).sub (hg_pp ⟨z, hz⟩)).differentiableAt
    convert h using 1
    funext w
    simp
  · exact (hf.sub hg).differentiableAt (hS.isOpen_compl.mem_nhds hz)

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
-- extends to a function analytic at every point of `Re s ≥ 1`; both parts in one statement.
example :
    (∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s | 1 ≤ s.re} ∧
        Set.EqOn F (fun s => Nat.Primes.logDirichletSeries s - 1 / (s - 1)) {s | 1 < s.re} :=
  ⟨fun _ hs => riemannZeta_ne_zero_of_one_le_re hs, Nat.Primes.logDirichletContinuation,
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
