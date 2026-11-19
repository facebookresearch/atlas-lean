/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import MathlibExt.Probability.KolmogorovContinuity

/-!
# Hölder continuity of Brownian paths

For every exponent `α < 1/2` and every horizon `T`, almost every path of a real Brownian motion is
`α`-Hölder continuous on `[0, T]`. This is the classical consequence of Kolmogorov's lemma: an
increment `B t - B s` is centered Gaussian with variance `|t - s|`, so
`E |B t - B s|^β = c_β |t - s|^{β/2}` for every `β > 0`, and Kolmogorov's lemma with exponents
`β` and `1 + κ = β / 2` gives a Hölder bound of every order `< κ / β = 1/2 - 1/β` on the dyadic
times; path continuity extends it to all times. Letting `β → ∞` covers every `α < 1/2`.

## Main results

* `ProbabilityTheory.integral_abs_rpow_gaussianReal`:
  `∫ |x|^β d N(0, v) = v^{β/2} ∫ |x|^β d N(0, 1)`.
* `ProbabilityTheory.IsBrownianReal.ae_holderOnWith`: **Hölder continuity of Brownian paths** of
  every order `α < 1/2` on every `[0, T]`.

## References

* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2, section "The continuity of sample paths".
* J.-F. Le Gall, *Mouvement brownien, processus de branchement et superprocessus* (DEA lecture
  notes, 1994), Lemme 2.3 (Kolmogorov's lemma).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- **Absolute moments of a centered Gaussian are integrable.** For `β > 0`, `|x|^β` is
integrable for the centered Gaussian law of any variance (all moments of a Gaussian are finite;
Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Chapter 1). -/
lemma integrable_abs_rpow_gaussianReal (v : ℝ≥0) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ ↦ |x| ^ β) (gaussianReal 0 v) := by
  lift β to ℝ≥0 using hβ.le
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) β).integrable_norm_rpow
    (by exact_mod_cast hβ.ne') ENNReal.coe_ne_top
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [ENNReal.coe_toReal, Real.norm_eq_abs, id]

/-- **Scaling of the absolute moments of a centered Gaussian.** For `β ≥ 0`,
`∫ |x|^β d N(0, v) = v^{β/2} ∫ |x|^β d N(0, 1)`, since `N(0, v)` is the image of `N(0, 1)` under
`x ↦ √v x` (Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Chapter 1). -/
lemma integral_abs_rpow_gaussianReal (v : ℝ≥0) {β : ℝ} (hβ : 0 ≤ β) :
    ∫ x : ℝ, |x| ^ β ∂gaussianReal 0 v =
      (v : ℝ) ^ (β / 2) * ∫ x : ℝ, |x| ^ β ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (Real.sqrt v * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  rw [← hmap, integral_map (measurable_const_mul _).aemeasurable
    (continuous_abs.rpow_const fun _ ↦ Or.inr hβ).aestronglyMeasurable]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ β = (v : ℝ) ^ (β / 2) * |x| ^ β := by
    intro x
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_eq_rpow, ← Real.rpow_mul (NNReal.coe_nonneg v)]
    ring_nf
  simp_rw [hpt]
  exact integral_const_mul _ _

private lemma tendsto_dyadicFloor (x : ℝ) :
    Tendsto (fun k : ℕ ↦ (⌊x * 2 ^ k⌋ : ℝ) / 2 ^ k) atTop (𝓝 x) := by
  have hup : ∀ k : ℕ, (⌊x * 2 ^ k⌋ : ℝ) / 2 ^ k ≤ x := fun k ↦ by
    rw [div_le_iff₀ (by positivity)]
    exact Int.floor_le _
  have hlow : ∀ k : ℕ, x - 1 / 2 ^ k ≤ (⌊x * 2 ^ k⌋ : ℝ) / 2 ^ k := fun k ↦ by
    rw [le_div_iff₀ (by positivity), sub_mul, one_div, inv_mul_cancel₀ (by positivity)]
    linarith [Int.lt_floor_add_one (x * 2 ^ k)]
  have hlim : Tendsto (fun k : ℕ ↦ x - 1 / (2 : ℝ) ^ k) atTop (𝓝 x) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_sub x
    simpa [one_div, inv_pow] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

private lemma dyadicFloor_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    (⌊x * 2 ^ k⌋ : ℝ) / 2 ^ k ∈
      MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Icc 0 1 := by
  refine ⟨⟨⌊x * 2 ^ k⌋, k, rfl⟩, ?_, ?_⟩
  · exact div_nonneg (by exact_mod_cast Int.floor_nonneg.2 (by positivity [hx.1])) (by positivity)
  · rw [div_le_iff₀ (by positivity), one_mul]
    exact (Int.floor_le _).trans (by nlinarith [hx.2, (by positivity : (0 : ℝ) < 2 ^ k)])

/-- **Hölder continuity of Brownian paths.** For every exponent `α < 1/2` and every horizon `T`,
almost every path of a Brownian motion is `α`-Hölder continuous on `[0, T]` (Le Gall, *Brownian
Motion, Martingales, and Stochastic Calculus*, Chapter 2, section "The continuity of sample
paths"). The proof applies Kolmogorov's lemma (Le Gall, DEA notes 1994, Lemme 2.3) to the moments
`E |B t - B s|^β = c_β |t - s|^{β/2}`. -/
theorem IsBrownianReal.ae_holderOnWith {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {α : ℝ≥0} (hα : α < 1 / 2) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0, HolderOnWith C α (fun t ↦ B t ω) (Set.Icc 0 T) := by
  have hP : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- exponents
  set a : ℝ := (α : ℝ) with ha_def
  have ha0 : 0 ≤ a := α.2
  have ha : a < 1 / 2 := by
    have : (α : ℝ) < ((1 / 2 : ℝ≥0) : ℝ) := by exact_mod_cast hα
    simpa using this
  set β : ℝ := 2 / (1 / 2 - a) with hβ_def
  have hden : 0 < 1 / 2 - a := by linarith
  have hβpos : 0 < β := div_pos two_pos hden
  set κ : ℝ := β / 2 - 1 with hκ_def
  have hβ2 : β / 2 = 1 / (1 / 2 - a) := by rw [hβ_def]; ring
  have hκ : 0 < κ := by
    have h1 : 1 < β / 2 := by rw [hβ2, lt_div_iff₀ hden]; linarith
    rw [hκ_def]; linarith
  have hκβ : κ / β = 1 / 4 + a / 2 := by
    have h1 : κ / β = 1 / 2 - 1 / β := by
      rw [hκ_def]
      field_simp
    rw [h1, hβ_def, one_div_div]
    ring
  set γ : ℝ := (a + (1 / 4 + a / 2)) / 2 with hγ_def
  have hγpos : 0 < γ := by rw [hγ_def]; positivity
  have hγlt : γ < κ / β := by rw [hκβ, hγ_def]; linarith
  have haγ : a ≤ γ := by rw [hγ_def]; linarith
  -- the time-rescaled process on `ℝ`
  set X : ℝ → Ω → ℝ := fun r ω ↦ B (Real.toNNReal (T * r)) ω with hX_def
  have hlaw : ∀ r r' : ℝ, HasLaw (fun ω ↦ X r ω - X r' ω)
      (gaussianReal 0 (nndist ((Real.toNNReal (T * r) : ℝ≥0) : ℝ)
        ((Real.toNNReal (T * r') : ℝ≥0) : ℝ))) P := fun r r' ↦ hB.hasLaw_sub _ _
  have hcontβ : Continuous fun x : ℝ ↦ |x| ^ β := continuous_abs.rpow_const fun _ ↦ Or.inr hβpos.le
  set m : ℝ := ∫ x : ℝ, |x| ^ β ∂gaussianReal 0 1 with hm_def
  have hm0 : 0 ≤ m := integral_nonneg fun x ↦ by positivity
  have hX_int : ∀ s t : ℝ, Integrable (fun ω ↦ |X s ω - X t ω| ^ β) P := fun s t ↦
    (hlaw s t).integrable_comp (f := fun x : ℝ ↦ |x| ^ β)
      (integrable_abs_rpow_gaussianReal _ hβpos)
  have hkolm : ∀ s t : ℝ,
      ∫ ω, |X s ω - X t ω| ^ β ∂P ≤ ((T : ℝ) ^ (β / 2) * m) * |s - t| ^ (1 + κ) := by
    intro s t
    have h1 := (hlaw s t).integral_comp (f := fun x : ℝ ↦ |x| ^ β) hcontβ.aestronglyMeasurable
    have h1' : ∫ ω, |X s ω - X t ω| ^ β ∂P =
        ∫ x : ℝ, |x| ^ β ∂gaussianReal 0 (nndist ((Real.toNNReal (T * s) : ℝ≥0) : ℝ)
          ((Real.toNNReal (T * t) : ℝ≥0) : ℝ)) := h1
    rw [h1', integral_abs_rpow_gaussianReal _ hβpos.le, ← hm_def]
    have hv : ((nndist ((Real.toNNReal (T * s) : ℝ≥0) : ℝ)
        ((Real.toNNReal (T * t) : ℝ≥0) : ℝ) : ℝ≥0) : ℝ) ≤ T * |s - t| := by
      rw [coe_nndist, Real.dist_eq, Real.coe_toNNReal', Real.coe_toNNReal']
      calc |max (T * s) 0 - max (T * t) 0| ≤ |T * s - T * t| := abs_max_sub_max_le_abs _ _ _
        _ = T * |s - t| := by rw [← mul_sub, abs_mul, abs_of_nonneg (NNReal.coe_nonneg T)]
    have hpow : ((nndist ((Real.toNNReal (T * s) : ℝ≥0) : ℝ)
        ((Real.toNNReal (T * t) : ℝ≥0) : ℝ) : ℝ≥0) : ℝ) ^ (β / 2) ≤
        (T : ℝ) ^ (β / 2) * |s - t| ^ (1 + κ) := by
      rw [show 1 + κ = β / 2 by rw [hκ_def]; ring,
        ← Real.mul_rpow (NNReal.coe_nonneg T) (abs_nonneg _)]
      exact Real.rpow_le_rpow (by positivity) hv (by positivity)
    calc _ ≤ (T : ℝ) ^ (β / 2) * |s - t| ^ (1 + κ) * m := mul_le_mul_of_nonneg_right hpow hm0
      _ = _ := by ring
  have hK : 0 ≤ (T : ℝ) ^ (β / 2) * m := by positivity
  have hdy := MathlibExt.Probability.KolmogorovContinuity.kolmogorov_ae_holder_on_dyadics
    hκ hβpos hK hX_int hkolm γ hγlt hγpos
  filter_upwards [hdy, hB.cont] with ω hCω hcont
  obtain ⟨C, hC, hCdy⟩ := hCω
  have hXc : Continuous fun r ↦ X r ω :=
    hcont.comp (continuous_real_toNNReal.comp (continuous_const.mul continuous_id))
  -- extension from the dyadic times to `[0, 1]`
  have hall : ∀ q r : ℝ, q ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |X q ω - X r ω| ≤ C * |q - r| ^ γ := by
    intro q r hq hr
    have h1 := (((hXc.tendsto q).comp (tendsto_dyadicFloor q)).sub
        ((hXc.tendsto r).comp (tendsto_dyadicFloor r))).abs
    have h2 := (tendsto_const_nhds (x := C)).mul
      (((Real.continuous_rpow_const hγpos.le).tendsto _).comp
        ((tendsto_dyadicFloor q).sub (tendsto_dyadicFloor r)).abs)
    exact le_of_tendsto_of_tendsto' h1 h2 fun k ↦
      hCdy _ _ (dyadicFloor_mem hq k) (dyadicFloor_mem hr k)
  -- rescale to `[0, T]` and lower the exponent from `γ` to `α`
  rcases eq_or_ne T 0 with hT | hT
  · refine ⟨0, fun s hs t ht ↦ ?_⟩
    have hs0 : s = 0 := le_antisymm (hT ▸ hs.2) hs.1
    have ht0 : t = 0 := le_antisymm (hT ▸ ht.2) ht.1
    simp [hs0, ht0]
  · have hTr : (0 : ℝ) < T := by exact_mod_cast pos_iff_ne_zero.2 hT
    refine ⟨(C * (T : ℝ) ^ (-a)).toNNReal, fun s hs t ht ↦ ?_⟩
    have hmem : ∀ u : ℝ≥0, u ∈ Icc 0 T → (u : ℝ) / T ∈ Icc (0 : ℝ) 1 := fun u hu ↦
      ⟨by positivity, by rw [div_le_one hTr]; exact_mod_cast hu.2⟩
    have hXu : ∀ u : ℝ≥0, X ((u : ℝ) / T) ω = B u ω := fun u ↦ by
      simp only [hX_def, mul_div_cancel₀ _ hTr.ne', Real.toNNReal_coe]
    have key := hall _ _ (hmem s hs) (hmem t ht)
    rw [hXu, hXu] at key
    have hq1 : |(s : ℝ) / T - t / T| ≤ 1 := by
      rw [abs_le]
      have hs' := hmem s hs
      have ht' := hmem t ht
      constructor <;> linarith [hs'.1, hs'.2, ht'.1, ht'.2]
    have hdown : |(s : ℝ) / T - t / T| ^ γ ≤ |(s : ℝ) / T - t / T| ^ a :=
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hq1 ha0 haγ
    have hscale : |(s : ℝ) / T - t / T| ^ a = (T : ℝ) ^ (-a) * |(s : ℝ) - t| ^ a := by
      rw [← sub_div, abs_div, abs_of_pos hTr, Real.div_rpow (abs_nonneg _) hTr.le,
        Real.rpow_neg hTr.le]
      ring
    have hbound : |B s ω - B t ω| ≤ C * (T : ℝ) ^ (-a) * |(s : ℝ) - t| ^ a := by
      calc |B s ω - B t ω| ≤ C * |(s : ℝ) / T - t / T| ^ γ := key
        _ ≤ C * |(s : ℝ) / T - t / T| ^ a := mul_le_mul_of_nonneg_left hdown hC.le
        _ = _ := by rw [hscale]; ring
    rw [edist_dist, edist_dist, Real.dist_eq, NNReal.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (NNReal.coe_nonneg α)]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * _
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hbound

end ProbabilityTheory
