/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.InitialInverseColeHopf
public import MathlibExt.Analysis.PDE.HeatKernelUniqueness
import MathlibExt.Analysis.PDE.BurgersExponentialGrowth

/-!
# Uniqueness for bounded classical Burgers solutions

For positive constant viscosity, a jointly continuous velocity on `[0,∞) × ℝ`
that is jointly `C²` and solves Burgers on `(0,∞) × ℝ` is uniquely determined
by its initial values, provided it is uniformly bounded on each finite time strip.
The bound may depend on the strip length. No initial spatial derivative or bound
on derivatives near zero is assumed. Values at negative times are unconstrained.

The initial-time inverse Cole–Hopf profile is identified with the Gaussian heat
solution by whole-line heat uniqueness. Taking its logarithmic spatial derivative
then identifies the velocity with the explicit `burgersSolution` construction.

The finite-strip statements restrict the required velocity bound, but retain the
whole-half-line continuity and regularity hypotheses. Finite-lifespan localization,
weak solutions, comparison and stability are not asserted here.
-/

@[expose] public section

open Set
open scoped ContDiff
open MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- The initial-time inverse profile equals the actual heat evolution of its initial data. -/
theorem initialInverseProfile_eq_heatSolution {u : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
      initialInverseProfile ν u a t x = heatSolution (initialHeatProfile ν (u 0) a) (ν * t) x := by
  have h0 : Continuous (u 0) := by
    rw [← continuousOn_univ]
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨le_rfl, hx⟩)
  have hb0 : ∃ M, ∀ x, |u 0 x| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, hM 0 ⟨le_rfl, hT⟩⟩
  apply eq_heatSolution_of_exp_growth hν (initialHeatProfile_contDiff h0 ν a).continuous
    (initialHeatProfile_hasExpGrowth hb0 hν a)
    ((initialInverseProfile_continuousOn hc ν a).mono (fun _ hp => ⟨hp.1.1, hp.2⟩))
    (fun t ht x => ?_)
    (fun t ht x => (initialInverseProfile_hasDerivAt_heat hc hu ht.1
      (hpde t ht.1) hν.ne' a x).hasDerivWithinAt)
    (fun _ _ _ => rfl) (initialInverseProfile_hasExpGrowthOnStrip hc hb ν a)
    (initialInverseProfile_zero ν u a)
  have hs : ContDiff ℝ 2 (u t) := by
    rw [← contDiffOn_univ]
    exact hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨ht.1, hx⟩)
  exact (initialInverseProfile_contDiff_space hs ν a).contDiffAt

/-- Every bounded classical competitor on a finite strip is the explicit Burgers solution. -/
theorem eq_burgersSolution_onStrip {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x, u t x = burgersSolution ν (u 0) a t x := by
  intro t ht x
  have hh := initialInverseProfile_eq_heatSolution hν (ht.1.trans ht.2) hc hu hb hpde a
  have hs : Continuous (u t) := by
    rw [← continuousOn_univ]
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨ht.1, hx⟩)
  have he : initialInverseProfile ν u a t = heatSolution (initialHeatProfile ν (u 0) a) (ν * t) :=
    funext (hh t ht)
  rw [← classicalTransform_initialInverseProfile hs hν.ne' a x]
  change -2 * ν * (deriv (initialInverseProfile ν u a t) x / initialInverseProfile ν u a t x) =
    -2 * ν * (deriv (heatSolution (initialHeatProfile ν (u 0) a) (ν * t)) x /
      heatSolution (initialHeatProfile ν (u 0) a) (ν * t) x)
  rw [he]

/-- Equal initial values determine the same bounded classical solution on a closed strip. -/
theorem burgers_eq_onStrip {u v : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hcu : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hv : ContDiffOn ℝ 2 (Function.uncurry v) (Ioi 0 ×ˢ univ))
    (hbu : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hbv : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M)
    (hpu : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (hpv : ∀ t, 0 < t → ∀ x,
      deriv (fun s => v s x) t + v t x * deriv (v t) x = ν * iteratedDeriv 2 (v t) x)
    (h0 : ∀ x, u 0 x = v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x = v t x := by
  intro t ht x
  rw [eq_burgersSolution_onStrip hν hcu hu hbu hpu 0 t ht x,
    eq_burgersSolution_onStrip hν hcv hv hbv hpv 0 t ht x, funext h0]

/-- Stripwise boundedness suffices for identification at every nonnegative time. -/
theorem eq_burgersSolution {u : ℝ → ℝ → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∀ T, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t, 0 ≤ t → ∀ x, u t x = burgersSolution ν (u 0) a t x :=
  fun t ht x => eq_burgersSolution_onStrip hν hc hu (hb t ht) hpde a t ⟨ht, le_rfl⟩ x

/-- Uniqueness on the nonnegative half-line, with bounds allowed to grow with strip length. -/
theorem burgers_eq {u v : ℝ → ℝ → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hcu : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hv : ContDiffOn ℝ 2 (Function.uncurry v) (Ioi 0 ×ˢ univ))
    (hbu : ∀ T, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hbv : ∀ T, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M)
    (hpu : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (hpv : ∀ t, 0 < t → ∀ x,
      deriv (fun s => v s x) t + v t x * deriv (v t) x = ν * iteratedDeriv 2 (v t) x)
    (h0 : ∀ x, u 0 x = v 0 x) : ∀ t, 0 ≤ t → ∀ x, u t x = v t x :=
  fun t ht x => burgers_eq_onStrip hν hcu hcv hu hv (hbu t ht) (hbv t ht) hpu hpv h0
    t ⟨ht, le_rfl⟩ x

end ColeHopf
