/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import MathlibExt.Probability.Statistics.Contiguity

/-!
# Girsanov's theorem for a constant drift

Under the exponential change of measure at time `T`, subtracting the drift `μ t` preserves
Brownian finite-dimensional laws up to `T`. The proof decomposes the process into the Brownian
bridge and the independent terminal value, whose Gaussian law is tilted by the density.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExt.Probability.GirsanovWanted

namespace IsBrownianReal

private lemma hasLaw_withDensity_comp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} {X : Ω → E} (hX : HasLaw X ν P)
    {w : E → ℝ≥0∞} (hw : Measurable w) :
    HasLaw X (ν.withDensity w) (P.withDensity (w ∘ X)) := by
  have hm := hX.aemeasurable.mono_ac (withDensity_absolutelyContinuous P (w ∘ X))
  refine ⟨hm, Measure.ext_of_lintegral _ fun f hf ↦ ?_⟩
  rw [lintegral_map' hf.aemeasurable hm]
  change ∫⁻ a, (f ∘ X) a ∂P.withDensity (w ∘ X) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (hw.comp_aemeasurable hX.aemeasurable) (hf.comp_aemeasurable hX.aemeasurable),
    lintegral_withDensity_eq_lintegral_mul _ hw hf]
  exact hX.lintegral_comp (hw.mul hf).aemeasurable

private lemma indepFun_bridge_endpoint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (T : ℝ≥0) (I : Finset ℝ≥0)
    (hI : ∀ t ∈ I, t ≤ T) (a : I → ℝ) (ha : ∀ i, a i * T = i.val) :
    IndepFun (fun ω (i : I) ↦ B i ω - a i * B T ω) (B T) P := by
  let J := insert T I
  let t : J := ⟨T, Finset.mem_insert_self ..⟩
  let incl (i : I) : J := ⟨i, Finset.mem_insert_of_mem i.2⟩
  -- Treat the endpoint as a one-coordinate vector to test independence coordinatewise.
  let L : (J → ℝ) →L[ℝ] (I → ℝ) × (Unit → ℝ) :=
    { toFun x := (fun i ↦ x (incl i) - a i * x t, fun _ ↦ x t)
      map_add' x y := by
        ext <;> simp
        ring
      map_smul' c x := by
        ext <;> simp
        ring }
  have hG := (hB.isGaussianProcess.hasGaussianLaw J).map L
  have hprob := hB.isGaussianProcess.isProbabilityMeasure
  have hLp (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hind := HasGaussianLaw.indepFun_of_covariance_eval
    (X := fun (i : I) ω ↦ B i ω - a i * B T ω) (Y := fun (_ : Unit) ↦ B T) hG
    (fun i _ ↦ by
      rw [covariance_fun_sub_left (hLp i) ((hLp T).const_mul _) (hLp T),
        covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval,
        min_eq_left (hI _ i.2), min_self, ha, sub_self])
  exact hind.comp measurable_id (measurable_pi_apply ())

end IsBrownianReal

/-- **Girsanov's theorem for a constant drift** (the Cameron–Martin formula for `h(t) = μ t`).
Let `B` be a Brownian motion, `μ` real and `T ≥ 0`, and let `Q` be the probability measure with
density `exp(μ B_T - μ² T / 2)` with respect to `P`. Under `Q`, the process `B t - μ t`,
`0 ≤ t ≤ T`, has the finite-dimensional laws of Brownian motion (Le Gall, GTM 274, Chapter 5,
sections "Girsanov's theorem" and "A few applications of Girsanov's theorem", with the drift
`∫_0^t μ ds`). -/
theorem IsBrownianReal.hasLaw_sub_drift_withDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (μ : ℝ) (T : ℝ≥0)
    (I : Finset ℝ≥0) (hI : ∀ t ∈ I, t ≤ T) :
    HasLaw (fun ω ↦ I.restrict fun t ↦ B t ω - μ * t) (BrownianReal.projectiveFamily I)
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (μ * B T ω - μ ^ 2 * T / 2))) := by
  let a (i : I) : ℝ := i.val / (T : ℝ)
  have ha (i : I) : a i * T = i.val := by
    by_cases hT : T = 0
    · have hi : i.val = 0 := le_antisymm (hT ▸ hI _ i.2) zero_le
      simp [a, hi]
    · exact div_mul_cancel₀ _ (by exact_mod_cast hT)
  let R (ω : Ω) (i : I) := B i ω - a i * B T ω
  have hR : AEMeasurable R P := .of_eval fun i ↦
    (hB.aemeasurable i).sub (aemeasurable_const.mul (hB.aemeasurable T))
  have hprob := hB.isGaussianProcess.isProbabilityMeasure
  have hind := IsBrownianReal.indepFun_bridge_endpoint hB.toIsPreBrownianReal T I hI a ha
  have hpair := hind.hasLaw_prod (hasLaw_map hR) (hB.hasLaw_eval T)
  let w (x : ℝ) := ENNReal.ofReal (Real.exp (μ * x - μ ^ 2 * T / 2))
  have hw : Measurable w := by fun_prop
  have htilt := IsBrownianReal.hasLaw_withDensity_comp hpair (hw.comp measurable_snd)
  simp only [Function.comp_def] at htilt
  have hgauss : (gaussianReal 0 T).withDensity w = gaussianReal (μ * T) T :=
    Statistics.Contiguity.gaussianReal_withDensity_exp μ T
  rw [← prod_withDensity_right hw, hgauss] at htilt
  have hcenter : MeasurePreserving (fun x : ℝ ↦ x - μ * T)
      (gaussianReal (μ * T) T) (gaussianReal 0 T) :=
    ⟨by fun_prop, by simp [gaussianReal_map_sub_const]⟩
  have hcentered := ((MeasurePreserving.id (P.map R)).prod hcenter).hasLaw.comp htilt
  let restore (z : (I → ℝ) × ℝ) (i : I) := z.1 i + a i * z.2
  have hrestore : Measurable restore := by fun_prop
  have horiginal : HasLaw (fun ω ↦ restore (R ω, B T ω)) (BrownianReal.projectiveFamily I) P := by
    simpa [restore, R, Finset.restrict_def] using hB.hasLaw I
  have h := HasLaw.comp_of_hasLaw_comp hrestore.aemeasurable hpair hcentered horiginal
  apply h.congr
  exact Filter.Eventually.of_forall fun ω ↦ funext fun i ↦ by
    change B i ω - μ * i.val = (B i ω - a i * B T ω) + a i * (B T ω - μ * T)
    rw [← ha i]
    ring

end MathlibExt.Probability.GirsanovWanted
