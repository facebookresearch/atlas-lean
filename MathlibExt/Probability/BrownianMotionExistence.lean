/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import MathlibExt.Probability.KolmogorovContinuousModification
import MathlibExt.Probability.BrownianQuadraticVariation
import MathlibExt.Probability.OrnsteinUhlenbeck

/-!
# Existence of Brownian motion

Pinned Mathlib defines pre-Brownian motion (`ProbabilityTheory.IsPreBrownianReal`: the
finite-dimensional laws of Brownian motion) and Brownian motion
(`ProbabilityTheory.IsBrownianReal`: a pre-Brownian motion with almost surely continuous paths),
and the repository constructs a pre-Brownian motion on the path space `ℝ≥0 → ℝ` by Kolmogorov
extension (`ProbabilityTheory.exists_isPreBrownianReal_eval`). This file closes the gap between
the two notions, as in the classical construction: a pre-Brownian increment `B s - B t` is
Gaussian with variance `|s - t|`, so `E |B s - B t|⁴ = 3 |s - t|²`, and Kolmogorov's lemma (with
`p = 4`, `q = 2`) gives a modification with continuous paths, which is a Brownian motion.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.isKolmogorovProcess`: a pre-Brownian motion with measurable
  coordinates satisfies Kolmogorov's condition `E |B s - B t|⁴ ≤ 3 |s - t|²`.
* `ProbabilityTheory.IsPreBrownianReal.exists_isBrownianReal_modification`: every pre-Brownian
  motion with measurable coordinates has a modification with continuous paths, and that
  modification is a Brownian motion.
* `ProbabilityTheory.exists_isBrownianReal`: **Brownian motion exists**.

## References

* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Théorème 14.2.1 (existence of Brownian motion, proved there with the Haar–Schauder series),
  Lemme 14.2.2.
* J.-F. Le Gall, *Mouvement brownien, processus de branchement et superprocessus* (DEA lecture
  notes, 1994), Lemme 2.3 (Kolmogorov's lemma).
* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private lemma edist_rpow_four (a b : ℝ) :
    edist a b ^ (4 : ℝ) = ENNReal.ofReal ((a - b) ^ 4) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact Even.pow_abs ⟨2, rfl⟩ _

/-- **Kolmogorov's condition for pre-Brownian motion.** A pre-Brownian motion `B` with
measurable coordinates satisfies `E |B s - B t|⁴ ≤ 3 |s - t|²` for all times `s, t`, that is,
it is a Kolmogorov process with exponents `p = 4`, `q = 2` and constant `3`: the moment
hypothesis of Kolmogorov's lemma (Le Gall, DEA notes 1994, Lemme 2.3), with `d = 1` and
`ε = 1`. -/
theorem IsPreBrownianReal.isKolmogorovProcess (hB : IsPreBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) :
    IsKolmogorovProcess B P 4 2 3 := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hmeas (fun s t ↦ ?_)
    (by norm_num) (by norm_num)
  set v : ℝ≥0 := nndist s.1 t.1 with hv
  have hlaw := hB.hasLaw_sub s t
  have hint : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow
      (by norm_num : (4 : ℕ) ≠ 0)
    refine h.congr (ae_of_all _ fun x ↦ ?_)
    simp [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩]
  calc ∫⁻ ω, edist (B s ω) (B t ω) ^ (4 : ℝ) ∂P
      = ∫⁻ ω, (fun x : ℝ ↦ ENNReal.ofReal (x ^ 4)) ((B s - B t) ω) ∂P := by
        refine lintegral_congr fun ω ↦ ?_
        rw [edist_rpow_four]
        rfl
    _ = ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂gaussianReal 0 v :=
        hlaw.lintegral_comp
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 4)).aemeasurable
    _ = ENNReal.ofReal (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun x ↦ by positivity)).symm
    _ = ENNReal.ofReal (3 * (v : ℝ) ^ 2) := by rw [integral_pow_four_gaussianReal]
    _ = ((3 : ℝ≥0) : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, edist_nndist,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity)]
        congr 1
        · simp
        · rw [hv, ENNReal.ofReal_coe_nnreal]
          rfl
    _ ≤ _ := le_rfl

/-- **Brownian motion as a continuous modification of pre-Brownian motion.** Every pre-Brownian
motion `B` with measurable coordinates on a probability space has a modification `W` with
measurable coordinates and continuous paths (on every sample), and `W` is a Brownian motion.
The continuity comes from Kolmogorov's lemma (Le Gall, DEA notes 1994, Lemme 2.3), applied to
the fourth moments of the increments. Le Gall's ENS notes *Intégration, Probabilités et
Processus Aléatoires* obtain continuity differently, in the proof of Théorème 14.2.1, from the
uniform convergence of the Haar–Schauder (Lévy–Ciesielski) series. -/
theorem IsPreBrownianReal.exists_isBrownianReal_modification [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hmeas : ∀ t, Measurable (B t)) :
    ∃ W : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (W t)) ∧ (∀ ω, Continuous fun t ↦ W t ω) ∧
      (∀ t, W t =ᵐ[P] B t) ∧ IsBrownianReal W P := by
  obtain ⟨W, hWm, hWc, hWB, -, -⟩ :=
    MathlibExt.Probability.KolmogorovContinuousModification.exists_continuous_modification
      (hB.isKolmogorovProcess hmeas) (by norm_num : (1 : ℝ) < 2)
  exact ⟨W, hWm, hWc, hWB,
    { toIsPreBrownianReal := hB.congr fun t ↦ (hWB t).symm
      cont := ae_of_all _ hWc }⟩

/-- **Existence of Brownian motion.** There is a probability measure `μ` on the path space
`ℝ≥0 → ℝ` and a process `W` on it with continuous paths (on every sample) that is a Brownian
motion: its finite-dimensional laws are the Brownian ones (`W 0 = 0` a.s., independent centered
Gaussian increments with variance the length of the time interval). Le Gall, ENS notes
*Intégration, Probabilités et Processus Aléatoires*, Théorème 14.2.1 ("Le mouvement brownien
existe"); Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Chapter 2. -/
theorem exists_isBrownianReal :
    ∃ (μ : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ), IsProbabilityMeasure μ ∧
      (∀ t, Measurable (W t)) ∧ (∀ ω, Continuous fun t ↦ W t ω) ∧ IsBrownianReal W μ := by
  obtain ⟨μ, hB⟩ := exists_isPreBrownianReal_eval
  have : IsProbabilityMeasure μ := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, -, hW⟩ :=
    hB.exists_isBrownianReal_modification (fun t ↦ measurable_pi_apply t)
  exact ⟨μ, W, inferInstance, hWm, hWc, hW⟩

end ProbabilityTheory
