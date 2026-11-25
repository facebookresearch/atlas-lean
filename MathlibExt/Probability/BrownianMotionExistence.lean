/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Kolmogorov
import MathlibExt.Probability.BrownianQuadraticVariation
import MathlibExt.Probability.KolmogorovContinuousModification
import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Existence of a Brownian motion with continuous paths

Mathlib defines Brownian motion through its finite-dimensional laws (`IsPreBrownianReal`) and
almost surely continuous paths (`IsBrownianReal`). This file proves that a Brownian motion exists,
and that one exists together with an independent centered Gaussian variable of any variance, the
setting of a stationary start for a linear stochastic differential equation.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.isKolmogorovProcess`: a pre-Brownian motion with measurable
  coordinates satisfies the Kolmogorov condition `E |B s - B t|⁴ ≤ 3 |s - t|²`.
* `ProbabilityTheory.exists_isBrownianReal`: a Brownian motion exists (Wiener 1923).
* `ProbabilityTheory.exists_isBrownianReal_indepFun_gaussianReal`: for every `v ≥ 0` there is a
  Brownian motion `B` and a variable `X₀ ~ N(0, v)` independent of `B`.
* `ProbabilityTheory.IsPreBrownianReal.exists_isBrownianReal_modification`: every pre-Brownian
  motion with measurable coordinates on a probability space has a modification with measurable
  coordinates and continuous paths, and that modification is a Brownian motion.

## Implementation notes

The coordinate process on paths `ℝ≥0 → ℝ` under the Kolmogorov extension of the Brownian
finite-dimensional laws (`exists_isPreBrownianReal_eval`) is pre-Brownian. Its increments are
`N(0, |s - t|)` with fourth moment `3 |s - t|²` (`integral_pow_four_gaussianReal`), so the
Kolmogorov–Chentsov theorem (`exists_continuous_modification`, time exponent `2 > 1`) gives a
modification with continuous paths, which is a Brownian motion. For the independent start, the
increments after time `1` form a Brownian motion (`IsBrownianReal.shift`) independent of the path
up to time `1` (`IsPreBrownianReal.indepFun_shift`), and `X₀ = √v B 1 ~ N(0, v)`.

## References

* N. Wiener, *Differential-space*, J. Math. Phys. 2 (1923), 131–174.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 2.2 (the Kolmogorov–Čentsov theorem and the existence of Brownian motion).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- **Kolmogorov condition for Brownian increments.** A pre-Brownian motion with measurable
coordinates satisfies `E |B s - B t|⁴ ≤ 3 |s - t|²`, the Kolmogorov condition with exponents
`4` and `2` and constant `3`: the fourth moment of `N(0, |s - t|)`. -/
theorem IsPreBrownianReal.isKolmogorovProcess {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) : IsKolmogorovProcess B P 4 2 3 := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hm (fun s t => ?_) (by norm_num)
    (by norm_num)
  have hlaw := hB.hasLaw_sub s t
  have hint : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 (nndist s.1 t.1)) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := nndist s.1 t.1) 4).integrable_norm_pow
      (by norm_num)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [id_eq, Real.norm_eq_abs]
    norm_num [Even.pow_abs ⟨2, rfl⟩]
  have h1 : ∀ ω, edist (B s ω) (B t ω) ^ (4 : ℝ) = ENNReal.ofReal ((B s ω - B t ω) ^ 4) := by
    intro ω
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
      abs_of_nonneg (by positivity)]
  simp_rw [h1]
  have h2 : ∫⁻ ω, ENNReal.ofReal ((B s ω - B t ω) ^ 4) ∂P =
      ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 (nndist s.1 t.1)) := by
    rw [← hlaw.lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (x ^ 4)) (by fun_prop)]
    rfl
  rw [h2, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity),
    integral_pow_four_gaussianReal, edist_dist,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num),
    show ((3 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply le_of_eq
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, coe_nndist, Real.dist_eq,
    NNReal.dist_eq, sq_abs, sq_abs]
  rfl

/-- **Existence of Brownian motion** (Wiener 1923). There is a probability measure on paths
`ℝ≥0 → ℝ` and a process on it that is a Brownian motion: Brownian finite-dimensional laws and
continuous paths. -/
theorem exists_isBrownianReal :
    ∃ μ : Measure (ℝ≥0 → ℝ), ∃ B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, IsBrownianReal B μ := by
  obtain ⟨μ, hB⟩ := exists_isPreBrownianReal_eval
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Y, -, hYc, hYae, -, -⟩ :=
    MathlibExt.Probability.KolmogorovContinuousModification.exists_continuous_modification
      (hB.isKolmogorovProcess (fun t => measurable_pi_apply t)) (by norm_num : (1 : ℝ) < 2)
  have hY : IsBrownianReal Y μ :=
    { toIsPreBrownianReal := hB.congr fun t => (hYae t).symm
      cont := ae_of_all _ hYc }
  exact ⟨μ, Y, hY⟩

/-- **Brownian motion with an independent Gaussian start.** For every `v ≥ 0` there is a Brownian
motion `B` and a variable `X₀ ~ N(0, v)` independent of the path process of `B`. -/
theorem exists_isBrownianReal_indepFun_gaussianReal (v : ℝ≥0) :
    ∃ μ : Measure (ℝ≥0 → ℝ), ∃ B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, ∃ X₀ : (ℝ≥0 → ℝ) → ℝ,
      IsBrownianReal B μ ∧ HasLaw X₀ (gaussianReal 0 v) μ ∧
        IndepFun X₀ (fun ω t ↦ B t ω) μ := by
  obtain ⟨μ, W, hW⟩ := exists_isBrownianReal
  refine ⟨μ, fun t ω ↦ W (1 + t) ω - W 1 ω, fun ω ↦ √(v : ℝ) * W 1 ω, hW.shift 1, ?_, ?_⟩
  · have hmap : HasLaw (fun x : ℝ ↦ √(v : ℝ) * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
      refine ⟨by fun_prop, ?_⟩
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        simp
    exact hmap.comp (hW.hasLaw_eval 1)
  · have hind := (hW.toIsPreBrownianReal.indepFun_shift 1).symm
    have h1 : (1 : ℝ≥0) ∈ Set.Iic 1 := Set.mem_Iic.mpr le_rfl
    exact hind.comp (φ := fun f : Set.Iic (1 : ℝ≥0) → ℝ ↦ √(v : ℝ) * f ⟨1, h1⟩)
      (ψ := id) ((measurable_pi_apply _).const_mul _) measurable_id

/-- **Brownian motion as a continuous modification of pre-Brownian motion.** Every pre-Brownian
motion `B` with measurable coordinates on a probability space has a modification `W` with
measurable coordinates and continuous paths (on every sample), and `W` is a Brownian motion.
The continuity comes from Kolmogorov's lemma (Le Gall, *Mouvement brownien, processus de
branchement et superprocessus*, DEA lecture notes, 1994, Lemme 2.3), applied to the fourth
moments of the increments (`IsPreBrownianReal.isKolmogorovProcess`). Le Gall's ENS notes
*Intégration, Probabilités et Processus Aléatoires* obtain continuity differently, in the proof
of Théorème 14.2.1, from the uniform convergence of the Haar–Schauder (Lévy–Ciesielski)
series. -/
theorem IsPreBrownianReal.exists_isBrownianReal_modification {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) :
    ∃ W : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (W t)) ∧ (∀ ω, Continuous fun t ↦ W t ω) ∧
      (∀ t, W t =ᵐ[P] B t) ∧ IsBrownianReal W P := by
  obtain ⟨W, hWm, hWc, hWB, -, -⟩ :=
    MathlibExt.Probability.KolmogorovContinuousModification.exists_continuous_modification
      (hB.isKolmogorovProcess hmeas) (by norm_num : (1 : ℝ) < 2)
  exact ⟨W, hWm, hWc, hWB,
    { toIsPreBrownianReal := hB.congr fun t ↦ (hWB t).symm
      cont := ae_of_all _ hWc }⟩

end ProbabilityTheory
