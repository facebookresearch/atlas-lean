/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

open scoped Topology

open scoped ContDiff ENNReal NNReal

/-!
# Weierstrass preparation theorem in `E × ℂ`
-/

namespace MathlibExt.Analysis.Complex.WeierstrassPreparationWanted

/-- Uniform Cauchy-type bound for a re-centered power series. -/
private theorem wprep_changeOrigin_norm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {W F : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 W F) {r₁ r' : ℝ≥0} (hr' : 0 < r')
    (hr : (r₁ : ℝ≥0∞) + (r' : ℝ≥0∞) < p.radius) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : W), ‖y‖ ≤ (r₁ : ℝ) →
      ∀ k : ℕ, ‖p.changeOrigin y k‖ ≤ C / (r' : ℝ) ^ k := by
  have hsumm : Summable (fun s : (Σ k l : ℕ,
      { s : Finset (Fin (k + l)) // s.card = l }) =>
      ‖p (s.1 + s.2.1)‖₊ * r₁ ^ s.2.1 * r' ^ s.1) :=
    p.changeOriginSeries_summable_aux₁ hr
  refine ⟨((∑' s : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
      ‖p (s.1 + s.2.1)‖₊ * r₁ ^ s.2.1 * r' ^ s.1 : ℝ≥0) : ℝ),
    NNReal.coe_nonneg _, fun y hy k => ?_⟩
  have hy1 : ‖y‖₊ ≤ r₁ := NNReal.coe_le_coe.mpr hy
  have hylt : (‖y‖₊ : ℝ≥0∞) < p.radius := by
    have h1 : (‖y‖₊ : ℝ≥0∞) ≤ (r₁ : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hy1
    have h2 : (r₁ : ℝ≥0∞) + 0 < (r₁ : ℝ≥0∞) + (r' : ℝ≥0∞) := by
      have h2' : r₁ + 0 < r₁ + r' := add_lt_add_right hr' r₁
      exact_mod_cast h2'
    calc (‖y‖₊ : ℝ≥0∞) ≤ (r₁ : ℝ≥0∞) + 0 := by rwa [add_zero]
      _ < (r₁ : ℝ≥0∞) + (r' : ℝ≥0∞) := h2
      _ < p.radius := hr
  have hfib : Summable (fun s : (Σ l : ℕ,
      { s : Finset (Fin (k + l)) // s.card = l }) =>
      ‖p (k + s.1)‖₊ * ‖y‖₊ ^ s.1) :=
    p.changeOriginSeries_summable_aux₂ hylt k
  have hfib' : Summable (fun s : (Σ l : ℕ,
      { s : Finset (Fin (k + l)) // s.card = l }) =>
      ‖p (k + s.1)‖₊ * r₁ ^ s.1 * r' ^ k) :=
    (NNReal.summable_sigma.1 hsumm).1 k
  have hle_fib : (∑' s : (Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
      ‖p (k + s.1)‖₊ * ‖y‖₊ ^ s.1 * r' ^ k)
      ≤ (∑' s : (Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
        ‖p (k + s.1)‖₊ * r₁ ^ s.1 * r' ^ k) := by
    apply Summable.tsum_le_tsum _ (hfib.mul_right _) hfib'
    intro s
    apply mul_le_mul_left _ _
    apply mul_le_mul_right _ _
    exact pow_le_pow_left₀ zero_le hy1 _
  have hnn := p.nnnorm_changeOrigin_le k hylt
  have hfib_le_total : (∑' s : (Σ l : ℕ,
      { s : Finset (Fin (k + l)) // s.card = l }),
      ‖p (k + s.1)‖₊ * r₁ ^ s.1 * r' ^ k)
      ≤ (∑' s : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
        ‖p (s.1 + s.2.1)‖₊ * r₁ ^ s.2.1 * r' ^ s.1) := by
    have hinj : Function.Injective (@Sigma.mk ℕ
        (fun k' => Σ l : ℕ, { s : Finset (Fin (k' + l)) // s.card = l }) k) :=
      sigma_mk_injective
    calc (∑' s : (Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
          ‖p (k + s.1)‖₊ * r₁ ^ s.1 * r' ^ k)
        = (∑' s : (Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
          (fun t : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) =>
            ‖p (t.1 + t.2.1)‖₊ * r₁ ^ t.2.1 * r' ^ t.1) (Sigma.mk k s)) := rfl
      _ ≤ (∑' t : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
          ‖p (t.1 + t.2.1)‖₊ * r₁ ^ t.2.1 * r' ^ t.1) :=
        NNReal.tsum_comp_le_tsum_of_inj hsumm hinj
  have key : ‖p.changeOrigin y k‖₊ * r' ^ k ≤
      (∑' s : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
        ‖p (s.1 + s.2.1)‖₊ * r₁ ^ s.2.1 * r' ^ s.1) := by
    calc ‖p.changeOrigin y k‖₊ * r' ^ k
        ≤ (∑' s : (Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
            ‖p (k + s.1)‖₊ * ‖y‖₊ ^ s.1) * r' ^ k :=
          mul_le_mul_left hnn _
      _ = (∑' s : (Σ l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
            ‖p (k + s.1)‖₊ * ‖y‖₊ ^ s.1 * r' ^ k) :=
          (NNReal.tsum_mul_right _ _).symm
      _ ≤ _ := hle_fib.trans hfib_le_total
  have hle : ‖p.changeOrigin y k‖₊ ≤
      (∑' s : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }),
        ‖p (s.1 + s.2.1)‖₊ * r₁ ^ s.2.1 * r' ^ s.1) / r' ^ k :=
    (le_div_iff₀ (pow_pos hr' k)).mpr key
  have hleR := NNReal.coe_le_coe.mpr hle
  rw [NNReal.coe_div, NNReal.coe_pow] at hleR
  exact hleR

/-- Term-by-term integration of a re-centered series along an arc. -/
private theorem wprep_hasSum_arc_integral_changeOrigin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V × ℂ → ℂ) (p : FormalMultilinearSeries ℂ (V × ℂ) ℂ)
    (v₀ : V) (ζ₁ : ℂ) (r : ℝ≥0∞)
    (hH : HasFPowerSeriesOnBall H p (v₀, ζ₁) r)
    (s : ℝ≥0) (hs0 : 0 < s) (hss : ((s + s : ℝ≥0) : ℝ≥0∞) < r)
    (c : ℂ) (R : ℝ) (θ₁ θ₂ : ℝ)
    (hcov : ∀ θ ∈ Set.uIcc θ₁ θ₂, ‖circleMap c R θ - ζ₁‖ ≤ (s : ℝ))
    (h : V) (hh : ‖h‖ < (s : ℝ)) :
    HasSum (fun k : ℕ => ∫ θ in θ₁..θ₂,
        deriv (circleMap c R) θ • ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k)
          fun _ => (h, (0 : ℂ))))
      (∫ θ in θ₁..θ₂, deriv (circleMap c R) θ • H (v₀ + h, circleMap c R θ)) := by
  have hrad : (0:ℝ≥0∞) < p.radius :=
    lt_of_le_of_lt zero_le (lt_of_lt_of_le hss hH.r_le)
  have hs_lt_radius : ((s : ℝ≥0) : ℝ≥0∞) < p.radius := by
    have h1 : ((s : ℝ≥0) : ℝ≥0∞) ≤ (((s + s : ℝ≥0))) := by
      rw [ENNReal.coe_add]
      exact le_add_of_nonneg_right zero_le
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hss hH.r_le)
  have hradius : (s : ℝ≥0∞) + (s : ℝ≥0∞) < p.radius := by
    have h := lt_of_lt_of_le hss hH.r_le
    rwa [ENNReal.coe_add] at h
  obtain ⟨C, hC0, hC⟩ := wprep_changeOrigin_norm_le p hs0 hradius
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs0
  have hqs : ‖h‖ / (s:ℝ) < 1 := by
    rw [div_lt_one hsR]
    exact hh
  have hqs0 : 0 ≤ ‖h‖ / (s:ℝ) := div_nonneg (norm_nonneg _) hsR.le
  have hsumable : Summable fun n => |R| * C * (‖h‖ / (s:ℝ)) ^ n :=
    (summable_geometric_of_lt_one hqs0 hqs).mul_left _
  have hderiv_cont : Continuous (fun θ => deriv (circleMap c R) θ) := by
    have hfun : (fun θ => deriv (circleMap c R) θ)
        = (fun θ => circleMap 0 R θ * Complex.I) :=
      funext (fun θ => deriv_circleMap c R θ)
    rw [hfun]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hderiv : ∀ θ : ℝ, ‖deriv (circleMap c R) θ‖ = |R| := by
    intro θ
    rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k θ => |R| * C * (‖h‖ / (s:ℝ)) ^ k) ?_ ?_ ?_ ?_ ?_
  · -- measurability of each summand
    intro n
    have hseries : ContinuousOn (fun y : V × ℂ => p.changeOrigin y n)
        (Metric.eball 0 p.radius) :=
      (p.hasFPowerSeriesOnBall_changeOrigin n hrad).continuousOn
    have hinner : ContinuousOn (fun θ => ((0 : V), circleMap c R θ - ζ₁))
        (Set.uIoc θ₁ θ₂) :=
      (continuous_const.prodMk
        ((continuous_circleMap c R).sub continuous_const)).continuousOn
    have hmaps : Set.MapsTo (fun θ => ((0 : V), circleMap c R θ - ζ₁))
        (Set.uIoc θ₁ θ₂) (Metric.eball (0 : V × ℂ) p.radius) := by
      intro θ hθ
      have hyleR : ‖((0 : V), circleMap c R θ - ζ₁)‖ ≤ (s : ℝ) := by
        simpa [Prod.norm_mk] using hcov θ (Set.uIoc_subset_uIcc hθ)
      have g2 : ‖((0 : V), circleMap c R θ - ζ₁)‖₊ ≤ s :=
        NNReal.coe_le_coe.mpr hyleR
      rw [mem_eball_zero_iff, enorm_eq_nnnorm]
      calc ((‖((0 : V), circleMap c R θ - ζ₁)‖₊ : ℝ≥0) : ℝ≥0∞)
          ≤ ((s : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr g2
        _ < p.radius := hs_lt_radius
    have hcoeff : ContinuousOn
        (fun θ => (p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) fun _ => (h, (0 : ℂ)))
        (Set.uIoc θ₁ θ₂) := by
      have houter : ContinuousOn
          (fun y : V × ℂ => (p.changeOrigin y n) fun _ => (h, (0 : ℂ)))
          (Metric.eball 0 p.radius) :=
        (ContinuousMultilinearMap.apply ℂ _ _ (fun _ => (h, (0 : ℂ)))).continuous.comp_continuousOn
          hseries
      exact houter.comp hinner hmaps
    have hcont : ContinuousOn
        (fun θ => deriv (circleMap c R) θ •
          ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) fun _ => (h, (0 : ℂ))))
        (Set.uIoc θ₁ θ₂) :=
      hderiv_cont.continuousOn.smul hcoeff
    exact hcont.aestronglyMeasurable measurableSet_uIoc
  · -- pointwise norm bound
    intro n
    apply Filter.Eventually.of_forall
    intro θ hθ
    have hyle : ‖((0 : V), circleMap c R θ - ζ₁)‖ ≤ (s:ℝ) := by
      simpa [Prod.norm_mk] using hcov θ (Set.uIoc_subset_uIcc hθ)
    have hN1 := hC ((0 : V), circleMap c R θ - ζ₁) hyle n
    have hop : ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) fun _ => (h, (0 : ℂ))‖
        ≤ ‖p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n‖ * ‖h‖ ^ n := by
      have hle := ContinuousMultilinearMap.le_opNorm
        (p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) (fun _ => (h, (0 : ℂ)))
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
      have hnorm : (‖(h, (0 : ℂ))‖ : ℝ) = ‖h‖ := by
        rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      rwa [hnorm] at hle
    have hS : (0:ℝ) < (s:ℝ) ^ n := pow_pos hsR n
    have hMC : ‖p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n‖ * ‖h‖ ^ n
        ≤ C / (s:ℝ) ^ n * ‖h‖ ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      exact hN1
    calc ‖deriv (circleMap c R) θ •
          ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) fun _ => (h, (0 : ℂ)))‖
        = ‖deriv (circleMap c R) θ‖ *
          ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) fun _ => (h, (0 : ℂ))‖ :=
          norm_smul _ _
      _ = |R| * ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n) fun _ => (h, (0 : ℂ))‖ := by
          rw [hderiv]
      _ ≤ |R| * (‖p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) n‖ * ‖h‖ ^ n) := by
          gcongr
      _ ≤ |R| * (C / (s:ℝ) ^ n * ‖h‖ ^ n) :=
          mul_le_mul_of_nonneg_left hMC (abs_nonneg _)
      _ = |R| * C * (‖h‖ / (s:ℝ)) ^ n := by
          rw [div_pow]
          ring
  · -- summability of the bound
    apply Filter.Eventually.of_forall
    intro θ _
    exact hsumable
  · -- integrability of the summed bound
    rw [show (fun t => ∑' n, |R| * C * (‖h‖ / (s:ℝ)) ^ n)
        = fun _ => |R| * C * (1 - ‖h‖ / (s:ℝ))⁻¹ from
      funext (fun t => by rw [tsum_mul_left, tsum_geometric_of_lt_one hqs0 hqs])]
    exact intervalIntegrable_const
  · -- pointwise sums
    apply Filter.Eventually.of_forall
    intro θ hθ
    have hyle : ‖((0 : V), circleMap c R θ - ζ₁)‖ ≤ (s:ℝ) := by
      simpa [Prod.norm_mk] using hcov θ (Set.uIoc_subset_uIcc hθ)
    have hylt : ((‖((0 : V), circleMap c R θ - ζ₁)‖₊ : ℝ≥0) : ℝ≥0∞) < r := by
      have g2 : ‖((0 : V), circleMap c R θ - ζ₁)‖₊ ≤ s :=
        NNReal.coe_le_coe.mpr hyle
      have g1 : ((‖((0 : V), circleMap c R θ - ζ₁)‖₊ : ℝ≥0) : ℝ≥0∞)
          ≤ (((s + s : ℝ≥0)) : ℝ≥0∞) := by
        have g3 : ‖((0 : V), circleMap c R θ - ζ₁)‖₊ ≤ s + s :=
          le_trans g2 (le_add_of_nonneg_right zero_le)
        exact ENNReal.coe_le_coe.mpr g3
      exact lt_of_le_of_lt g1 hss
    have hco := hH.changeOrigin (y := ((0 : V), circleMap c R θ - ζ₁)) hylt
    have h10 : ‖(h, (0 : ℂ))‖ = ‖h‖ := by
      rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    have hmem : (h, (0 : ℂ)) ∈
        Metric.eball (0 : V × ℂ) (r - ‖((0 : V), circleMap c R θ - ζ₁)‖₊) := by
      have g1 : ‖(h, (0 : ℂ))‖₊ < s := by
        rw [← NNReal.coe_lt_coe, coe_nnnorm, h10]
        exact hh
      have g2 : ‖((0 : V), circleMap c R θ - ζ₁)‖₊ ≤ s :=
        NNReal.coe_le_coe.mpr hyle
      have g3 : ‖(h, (0 : ℂ))‖₊ + ‖((0 : V), circleMap c R θ - ζ₁)‖₊ < s + s :=
        add_lt_add_of_lt_of_le g1 g2
      have g4 : ((‖(h, (0 : ℂ))‖₊ + ‖((0 : V), circleMap c R θ - ζ₁)‖₊ : ℝ≥0) : ℝ≥0∞)
          < (((s + s : ℝ≥0)) : ℝ≥0∞) := by
        exact_mod_cast g3
      rw [ENNReal.coe_add] at g4
      have g5 : ((‖(h, (0 : ℂ))‖₊ : ℝ≥0) : ℝ≥0∞) +
          ((‖((0 : V), circleMap c R θ - ζ₁)‖₊ : ℝ≥0) : ℝ≥0∞) < r :=
        lt_of_lt_of_le g4 (le_of_lt hss)
      rw [mem_eball_zero_iff, enorm_eq_nnnorm, lt_tsub_iff_right]
      exact g5
    have hsum := hco.hasSum hmem
    have hcenter : (v₀, ζ₁) + ((0 : V), circleMap c R θ - ζ₁) + (h, 0)
        = (v₀ + h, circleMap c R θ) := by
      ext <;> simp
    rw [hcenter] at hsum
    exact hsum.const_smul _

/-- Analyticity of an arc integral in the parameter. -/
private theorem wprep_analyticAt_arc_integral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V × ℂ → ℂ) (p : FormalMultilinearSeries ℂ (V × ℂ) ℂ)
    (v₀ : V) (ζ₁ : ℂ) (r : ℝ≥0∞)
    (hH : HasFPowerSeriesOnBall H p (v₀, ζ₁) r)
    (s : ℝ≥0) (hs0 : 0 < s) (hss : ((s + s : ℝ≥0) : ℝ≥0∞) < r)
    (c : ℂ) (R : ℝ) (θ₁ θ₂ : ℝ)
    (hcov : ∀ θ ∈ Set.uIcc θ₁ θ₂, ‖circleMap c R θ - ζ₁‖ ≤ (s : ℝ)) :
    AnalyticAt ℂ (fun v => ∫ θ in θ₁..θ₂,
      deriv (circleMap c R) θ • H (v, circleMap c R θ)) v₀ := by
  have hrad : (0:ℝ≥0∞) < p.radius :=
    lt_of_le_of_lt zero_le (lt_of_lt_of_le hss hH.r_le)
  have hradius : (s : ℝ≥0∞) + (s : ℝ≥0∞) < p.radius := by
    have h := lt_of_lt_of_le hss hH.r_le
    rwa [ENNReal.coe_add] at h
  obtain ⟨C, hC0, hC⟩ := wprep_changeOrigin_norm_le p hs0 hradius
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs0
  have hderiv : ∀ θ : ℝ, ‖deriv (circleMap c R) θ‖ = |R| := by
    intro θ
    rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  have hderiv_cont : Continuous (fun θ => deriv (circleMap c R) θ) := by
    have hfun : (fun θ => deriv (circleMap c R) θ)
        = (fun θ => circleMap 0 R θ * Complex.I) :=
      funext (fun θ => deriv_circleMap c R θ)
    rw [hfun]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hinner : ContinuousOn (fun θ => ((0 : V), circleMap c R θ - ζ₁))
      (Set.uIcc θ₁ θ₂) :=
    (continuous_const.prodMk
      ((continuous_circleMap c R).sub continuous_const)).continuousOn
  have hmaps : Set.MapsTo (fun θ => ((0 : V), circleMap c R θ - ζ₁))
      (Set.uIcc θ₁ θ₂) (Metric.eball (0 : V × ℂ) p.radius) := by
    intro θ hθ
    have hyleR : ‖((0 : V), circleMap c R θ - ζ₁)‖ ≤ (s : ℝ) := by
      simpa [Prod.norm_mk] using hcov θ hθ
    have g2 : ‖((0 : V), circleMap c R θ - ζ₁)‖₊ ≤ s :=
      NNReal.coe_le_coe.mpr hyleR
    have hs_lt : ((s : ℝ≥0) : ℝ≥0∞) < p.radius := by
      have h1 : ((s : ℝ≥0) : ℝ≥0∞) ≤ (((s + s : ℝ≥0))) := by
        rw [ENNReal.coe_add]
        exact le_add_of_nonneg_right zero_le
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hss hH.r_le)
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    calc ((‖((0 : V), circleMap c R θ - ζ₁)‖₊ : ℝ≥0) : ℝ≥0∞)
        ≤ ((s : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr g2
      _ < p.radius := hs_lt
  set Q : FormalMultilinearSeries ℂ V ℂ := fun k =>
    ∫ θ in θ₁..θ₂, deriv (circleMap c R) θ •
      ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℂ V ℂ)) with hQdef
  have hseries : ∀ k : ℕ, ContinuousOn (fun y : V × ℂ => p.changeOrigin y k)
      (Metric.eball 0 p.radius) := fun k =>
    (p.hasFPowerSeriesOnBall_changeOrigin k hrad).continuousOn
  have hcontMl : ∀ k : ℕ, ContinuousOn
      (fun θ => deriv (circleMap c R) θ •
        ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl ℂ V ℂ)))
      (Set.uIcc θ₁ θ₂) := by
    intro k
    have hM : ContinuousOn
        (fun θ => (p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl ℂ V ℂ))
        (Set.uIcc θ₁ θ₂) := by
      have hcomp : Continuous (fun M : ContinuousMultilinearMap ℂ
          (fun _ : Fin k => V × ℂ) ℂ => M.compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl ℂ V ℂ)) :=
        ContinuousMultilinearMap.continuous_precomp _
      exact (hcomp.comp_continuousOn (hseries k)).comp hinner hmaps
    exact hderiv_cont.continuousOn.smul hM
  have heval : ∀ (k : ℕ) (hh : V),
      Q k (fun _ => hh) = ∫ θ in θ₁..θ₂, deriv (circleMap c R) θ •
        ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k) fun _ => (hh, (0 : ℂ))) := by
    intro k hh
    have hint : IntervalIntegrable (fun θ => deriv (circleMap c R) θ •
        ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl ℂ V ℂ))) MeasureTheory.volume θ₁ θ₂ :=
      (hcontMl k).intervalIntegrable
    have hcomm := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => V) ℂ
      (fun _ => hh)).intervalIntegral_comp_comm hint
    calc Q k (fun _ => hh)
        = (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => V) ℂ (fun _ => hh)) (Q k) :=
          ContinuousMultilinearMap.apply_apply.symm
      _ = ∫ θ in θ₁..θ₂, (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => V) ℂ
          (fun _ => hh)) (deriv (circleMap c R) θ •
          ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inl ℂ V ℂ))) := by
          rw [hQdef]
          exact hcomm.symm
      _ = ∫ θ in θ₁..θ₂, deriv (circleMap c R) θ •
          ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k) fun _ => (hh, (0 : ℂ))) := by
          congr 1
  have hQbound : ∀ k : ℕ,
      ‖Q k‖ ≤ |θ₂ - θ₁| * (|R| * (C / (s:ℝ) ^ k)) := by
    intro k
    have hper : ∀ θ ∈ Set.uIoc θ₁ θ₂,
        ‖deriv (circleMap c R) θ •
          ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inl ℂ V ℂ))‖
        ≤ |R| * (C / (s:ℝ) ^ k) := by
      intro θ hθ
      have hyleR : ‖((0 : V), circleMap c R θ - ζ₁)‖ ≤ (s : ℝ) := by
        simpa [Prod.norm_mk] using hcov θ (Set.uIoc_subset_uIcc hθ)
      have hMk := hC ((0 : V), circleMap c R θ - ζ₁) hyleR k
      have hcomp : ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl ℂ V ℂ)‖ ≤ C / (s:ℝ) ^ k := by
        calc ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.inl ℂ V ℂ)‖
            ≤ ‖p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k‖ *
              ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℂ V ℂ‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ ≤ ‖p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k‖ * 1 := by
              have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℂ V ℂ‖ ≤ 1 := by
                refine Finset.prod_le_one₀ ?_ ?_
                · intro i _
                  exact norm_nonneg _
                · intro i _
                  exact ContinuousLinearMap.norm_inl_le_one ℂ V ℂ
              exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
          _ = ‖p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k‖ := mul_one _
          _ ≤ C / (s:ℝ) ^ k := hMk
      calc ‖deriv (circleMap c R) θ •
            ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.inl ℂ V ℂ))‖
          = ‖deriv (circleMap c R) θ‖ *
            ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.inl ℂ V ℂ)‖ := norm_smul _ _
        _ = |R| * ‖(p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inl ℂ V ℂ)‖ := by rw [hderiv]
        _ ≤ |R| * (C / (s:ℝ) ^ k) := by
            gcongr
    calc ‖Q k‖ ≤ (|R| * (C / (s:ℝ) ^ k)) * |θ₂ - θ₁| := by
            rw [hQdef]
            exact intervalIntegral.norm_integral_le_of_norm_le_const (fun θ hθ => hper θ hθ)
      _ = |θ₂ - θ₁| * (|R| * (C / (s:ℝ) ^ k)) := by ring
  have hrad_Q : ((s : ℝ≥0) : ℝ≥0∞) ≤ Q.radius := by
    refine Q.le_radius_of_bound (|θ₂ - θ₁| * (|R| * C)) fun k => ?_
    have hSk : (s:ℝ) ^ k ≠ 0 := (pow_pos hsR k).ne'
    calc ‖Q k‖ * (s:ℝ) ^ k
        ≤ (|θ₂ - θ₁| * (|R| * (C / (s:ℝ) ^ k))) * (s:ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (hQbound k) (pow_nonneg hsR.le k)
      _ = |θ₂ - θ₁| * (|R| * C) := by
          field_simp
  have hHB : HasFPowerSeriesOnBall (fun v => ∫ θ in θ₁..θ₂,
      deriv (circleMap c R) θ • H (v, circleMap c R θ)) Q v₀ ↑s := by
    refine ⟨hrad_Q, by exact_mod_cast hs0, fun {y} hy => ?_⟩
    rw [mem_eball_zero_iff, enorm_eq_nnnorm] at hy
    have hyR : ‖y‖ < (s:ℝ) := by
      have h2 : ‖y‖₊ < s := by exact_mod_cast hy
      exact_mod_cast h2
    have hN2 := wprep_hasSum_arc_integral_changeOrigin H p v₀ ζ₁ r hH s hs0 hss
      c R θ₁ θ₂ hcov y hyR
    have hterm : ∀ k : ℕ, (∫ θ in θ₁..θ₂, deriv (circleMap c R) θ •
        ((p.changeOrigin ((0 : V), circleMap c R θ - ζ₁) k) fun _ => (y, (0 : ℂ))))
        = Q k (fun _ => y) := fun k => (heval k y).symm
    simpa only [hterm] using hN2
  exact hHB.analyticAt

/-- Analyticity of a parametric circle integral. -/
private theorem wprep_analyticAt_circleIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V × ℂ → ℂ) (v₀ : V) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hH : ∀ ζ ∈ Metric.sphere c R, AnalyticAt ℂ H (v₀, ζ)) :
    AnalyticAt ℂ (fun v => ∮ ζ in C(c, R), H (v, ζ)) v₀ := by
  have hall : ∀ θ : ℝ, ∃ (p : FormalMultilinearSeries ℂ (V × ℂ) ℂ) (r : ℝ≥0∞),
      HasFPowerSeriesOnBall H p (v₀, circleMap c R θ) r ∧ ∃ (s : ℝ≥0),
        0 < s ∧ ((s + s : ℝ≥0) : ℝ≥0∞) < r := by
    intro θ
    have hmem : circleMap c R θ ∈ Metric.sphere c R :=
      circleMap_mem_sphere c hR.le θ
    obtain ⟨p, r, hpr⟩ := hH _ hmem
    obtain ⟨s₀, hs0a, hs0b⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpr.r_pos
    have hs0' : (0 : ℝ≥0) < s₀ := by exact_mod_cast hs0a
    refine ⟨p, r, hpr, s₀ / 2, by positivity, ?_⟩
    have hadd : s₀ / 2 + s₀ / 2 = s₀ := add_halves _
    calc (((s₀ / 2 + s₀ / 2 : ℝ≥0)) : ℝ≥0∞) = ((s₀ : ℝ≥0) : ℝ≥0∞) := by
          rw [hadd]
      _ < r := hs0b
  choose p r hpr s hs0 hss using hall
  have hopen : ∀ θ : ℝ, IsOpen
      (circleMap c R ⁻¹' Metric.ball (circleMap c R θ) (s θ)) :=
    fun θ => (continuous_circleMap c R).isOpen_preimage _ Metric.isOpen_ball
  have hcover : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ ⋃ θ : ℝ,
      circleMap c R ⁻¹' Metric.ball (circleMap c R θ) (s θ) := by
    intro t ht
    rw [Set.mem_iUnion]
    refine ⟨t, Metric.mem_ball_self ?_⟩
    show (0 : ℝ) < ((s t : ℝ≥0) : ℝ)
    exact_mod_cast hs0 t
  obtain ⟨δ, hδ0, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hcover
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.pi / δ)
  have h2pid : (0 : ℝ) < 2 * Real.pi / δ := div_pos (by positivity) hδ0
  have hnR : (0 : ℝ) < (n : ℝ) := lt_trans h2pid hn
  have hnR0 : ((n : ℕ) : ℝ) ≠ 0 := ne_of_gt hnR
  set t : ℕ → ℝ := fun k => 2 * Real.pi * k / n with ht
  have ht0 : t 0 = 0 := by simp [ht]
  have htn : t n = 2 * Real.pi := by
    rw [ht]
    beta_reduce
    exact mul_div_cancel_right₀ _ hnR0
  have hdiff : ∀ k : ℕ, t (k + 1) - t k = 2 * Real.pi / n := by
    intro k
    rw [ht]
    beta_reduce
    rw [← sub_div]
    congr 1
    push_cast
    ring
  have htle : ∀ k : ℕ, t k ≤ t (k + 1) := by
    intro k
    have hnn : (0 : ℝ) ≤ 2 * Real.pi / n := le_of_lt (div_pos (by positivity) hnR)
    linarith [hdiff k]
  have htk0 : ∀ k : ℕ, 0 ≤ t k := by
    intro k
    rw [ht]
    beta_reduce
    exact div_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg k))
      (Nat.cast_nonneg n)
  have htkn : ∀ k : ℕ, k ≤ n → t k ≤ 2 * Real.pi := by
    intro k hk
    rw [ht]
    beta_reduce
    have hkn : (k : ℝ) / n ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hk
    calc 2 * Real.pi * k / n = (2 * Real.pi) * ((k : ℝ) / n) := by ring
      _ ≤ 2 * Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hkn (by positivity)
      _ = 2 * Real.pi := mul_one _
  have h2pi : 2 * Real.pi / (n : ℝ) < δ := by
    rw [div_lt_iff₀ hnR]
    have h2 := (div_lt_iff₀ hδ0).mp hn
    linarith
  have hder : Continuous fun θ => deriv (circleMap c R) θ := by
    have hfun : (fun θ => deriv (circleMap c R) θ)
        = (fun θ => circleMap 0 R θ * Complex.I) :=
      funext (fun θ => deriv_circleMap c R θ)
    rw [hfun]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hAk : ∀ k ∈ Finset.range n, AnalyticAt ℂ (fun v =>
      ∫ θ in t k..t (k + 1), deriv (circleMap c R) θ • H (v, circleMap c R θ)) v₀ := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hmem : t k ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
      Set.mem_Icc.mpr ⟨htk0 k, htkn k (le_of_lt hkn)⟩
    obtain ⟨θk, hθk⟩ := hδ (t k) hmem
    have hcov : ∀ θ ∈ Set.uIcc (t k) (t (k + 1)),
        ‖circleMap c R θ - circleMap c R θk‖ ≤ ((s θk : ℝ≥0) : ℝ) := by
      intro θ hθ
      have hIk : θ ∈ Set.Icc (t k) (t (k + 1)) := by
        rw [← Set.uIcc_of_le (htle k)]
        exact hθ
      have hmem2 : θ ∈ Metric.ball (t k) δ := by
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ θ - t k by linarith [hIk.1])]
        have hle : θ - t k ≤ t (k + 1) - t k := by linarith [hIk.2]
        have hlt : t (k + 1) - t k < δ := by
          rw [hdiff k]
          exact h2pi
        linarith
      have hU : circleMap c R θ ∈ Metric.ball (circleMap c R θk) (s θk) :=
        hθk hmem2
      have hball : dist (circleMap c R θ) (circleMap c R θk)
          < ((s θk : ℝ≥0) : ℝ) :=
        Metric.mem_ball.mp hU
      rw [dist_eq_norm] at hball
      exact le_of_lt hball
    exact wprep_analyticAt_arc_integral H (p θk) v₀ (circleMap c R θk) (r θk)
      (hpr θk) (s θk) (hs0 θk) (hss θk) c R (t k) (t (k + 1)) hcov
  have hsumA : AnalyticAt ℂ (fun v => ∑ k ∈ Finset.range n,
      ∫ θ in t k..t (k + 1), deriv (circleMap c R) θ • H (v, circleMap c R θ)) v₀ :=
    Finset.analyticAt_fun_sum _ (fun k hk => hAk k hk)
  have hev : ∀ᶠ v in 𝓝 v₀, ∀ ζ ∈ Metric.sphere c R, AnalyticAt ℂ H (v, ζ) := by
    have hopen2 := isOpen_analyticAt ℂ H
    have hpt : ∀ ζ₀ ∈ Metric.sphere c R,
        ∀ᶠ p in 𝓝 (v₀, ζ₀), AnalyticAt ℂ H (p.1, p.2) := by
      intro ζ₀ hζ₀
      have hmem : (v₀, ζ₀) ∈ {x : V × ℂ | AnalyticAt ℂ H x} := hH ζ₀ hζ₀
      have hev0 : ∀ᶠ p in 𝓝 (v₀, ζ₀), p ∈ {x : V × ℂ | AnalyticAt ℂ H x} :=
        hopen2.mem_nhds hmem
      refine hev0.mono fun p hp => ?_
      rw [Prod.mk.eta]
      exact hp
    exact IsCompact.eventually_forall_of_forall_eventually (isCompact_sphere c R) hpt
  have heq : (fun v => ∑ k ∈ Finset.range n, ∫ θ in t k..t (k + 1),
        deriv (circleMap c R) θ • H (v, circleMap c R θ)) =ᶠ[𝓝 v₀]
      (fun v => ∮ ζ in C(c, R), H (v, ζ)) := by
    filter_upwards [hev] with v hv
    have hcv : ContinuousOn (fun ζ => H (v, ζ)) (Metric.sphere c R) := by
      refine continuousOn_of_forall_continuousAt fun ζ hζ => ?_
      have h1 : ContinuousAt H (v, ζ) := (hv ζ hζ).continuousAt
      have h2 : ContinuousAt (fun ζ' : ℂ => ((v, ζ') : V × ℂ)) ζ :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact h1.comp h2
    have hpiece : ∀ k < n, IntervalIntegrable
        (fun θ => deriv (circleMap c R) θ • H (v, circleMap c R θ))
        MeasureTheory.volume (t k) (t (k + 1)) := by
      intro k hk
      have hFc : ContinuousOn
          (fun θ => deriv (circleMap c R) θ • H (v, circleMap c R θ))
          (Set.uIcc (t k) (t (k + 1))) :=
        hder.continuousOn.smul (hcv.comp (continuous_circleMap c R).continuousOn
          (fun θ _ => circleMap_mem_sphere c hR.le θ))
      exact hFc.intervalIntegrable
    change (∑ k ∈ Finset.range n, ∫ θ in t k..t (k + 1),
        deriv (circleMap c R) θ • H (v, circleMap c R θ))
      = (∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap c R) θ • H (v, circleMap c R θ))
    have hbase := intervalIntegral.sum_integral_adjacent_intervals (a := t)
      (f := fun θ => deriv (circleMap c R) θ • H (v, circleMap c R θ)) hpiece
    rw [ht0, htn] at hbase
    exact hbase
  exact hsumA.congr heq

/-- Laurent-coefficient evaluation, vanishing part. -/
private theorem wprep_circleIntegral_pow_ratio_eq_zero
    (g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 ρ)) (n k : ℕ) (hnk : n ≤ k) :
    (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ k / ζ ^ n) = 0 := by
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  have hF : DifferentiableOn ℂ (fun ζ => g ζ * ζ ^ (k - n))
      (Metric.closedBall 0 ρ) :=
    hg.mul (differentiableOn_pow _)
  have hne : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ ≠ 0 := by
    intro ζ hζ hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
    linarith
  have hEq : Set.EqOn (fun ζ => g ζ * ζ ^ k / ζ ^ n)
      (fun ζ => g ζ * ζ ^ (k - n)) (Metric.sphere (0 : ℂ) ρ) := by
    intro ζ hζ
    change g ζ * ζ ^ k / ζ ^ n = g ζ * ζ ^ (k - n)
    rw [div_eq_mul_inv, mul_assoc, ← pow_sub₀ ζ (hne ζ hζ) hnk]
  rw [circleIntegral.integral_congr hρ0 hEq]
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ0
    Set.countable_empty hF.continuousOn (fun z hz => hF.differentiableAt
      (Metric.closedBall_mem_nhds_of_mem hz.1))

/-- Laurent-coefficient evaluation, residue part. -/
private theorem wprep_circleIntegral_pow_ratio_eq_two_pi_I
    (g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 ρ)) (n k : ℕ) (hnk : k + 1 = n) :
    (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ k / ζ ^ n) = 2 * Real.pi * Complex.I * g 0 := by
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  have hw : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hne : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ ≠ 0 := by
    intro ζ hζ hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
    linarith
  have hEq : Set.EqOn (fun ζ => g ζ * ζ ^ k / ζ ^ n)
      (fun ζ => (ζ - 0)⁻¹ • g ζ) (Metric.sphere (0 : ℂ) ρ) := by
    intro ζ hζ
    have hζ0 := hne ζ hζ
    have hζk : ζ ^ k ≠ 0 := pow_ne_zero _ hζ0
    subst hnk
    change g ζ * ζ ^ k / ζ ^ (k + 1) = (ζ - 0)⁻¹ • g ζ
    rw [sub_zero, smul_eq_mul]
    field_simp
    ring
  rw [circleIntegral.integral_congr hρ0 hEq, hg.circleIntegral_sub_inv_smul hw,
    smul_eq_mul]

/-- Geometric-sum quotient identity. -/
private theorem wprep_geom_div (x y : ℂ) (n : ℕ) (hxy : x ≠ y) :
    (x ^ n - y ^ n) / (x - y)
      = ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i) := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  exact ((eq_div_iff hsub).mpr (geom_sum₂_mul x y n)).symm

/-- Difference of monic-polynomial values, split off. -/
private theorem wprep_poly_sub (d : ℕ) (b : Fin d → ℂ) (ζ w : ℂ) :
    (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
      - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))
      = (ζ ^ d - w ^ d)
        + ∑ j : Fin d, b j * (ζ ^ (j : ℕ) - w ^ (j : ℕ)) := by
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => (mul_sub _ _ _).symm)

/-- Quotient of monic-polynomial values by `ζ - w`. -/
private theorem wprep_poly_div (d : ℕ) (b : Fin d → ℂ) (ζ w : ℂ) (hζw : ζ ≠ w) :
    ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
      - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)
      = (∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
        + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
          ζ ^ i * w ^ ((j : ℕ) - 1 - i) := by
  rw [wprep_poly_sub, add_div, wprep_geom_div ζ w d hζw]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc, wprep_geom_div ζ w (j : ℕ) hζw]

/-- Splitting of the Cauchy integrand. -/
private theorem wprep_split_integrand (d : ℕ) (b : Fin d → ℂ) (h : ℂ → ℂ)
    (ζ w : ℂ) (hP : ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ) ≠ 0) (hζw : ζ ≠ w) :
    (ζ - w)⁻¹ • h ζ
      = (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) *
          (h ζ / ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w)))
        + h ζ * (((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
            - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)) /
          (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) := by
  have hsub : ζ - w ≠ 0 := sub_ne_zero.mpr hζw
  have hS := wprep_poly_div d b ζ w hζw
  have hAD : (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w) ≠ 0 :=
    mul_ne_zero hP hsub
  rw [smul_eq_mul, inv_mul_eq_div, hS]
  have e1 : (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))
        * (h ζ / ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w)))
      = (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) * h ζ /
        ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w)) := by
    rw [mul_div_assoc]
  have e2 : h ζ * ((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
          + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
            ζ ^ i * w ^ ((j : ℕ) - 1 - i))
        / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
      = h ζ * ((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
          + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
            ζ ^ i * w ^ ((j : ℕ) - 1 - i)) * (ζ - w) /
        ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w)) := by
    rw [eq_div_iff hAD, ← mul_assoc, div_mul_cancel₀ _ hP]
  have hnum : (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) * h ζ
        + h ζ * ((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
          + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
            ζ ^ i * w ^ ((j : ℕ) - 1 - i)) * (ζ - w)
      = (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * h ζ := by
    have hSmul : ((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
          + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
            ζ ^ i * w ^ ((j : ℕ) - 1 - i)) * (ζ - w)
        = (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
          - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) := by
      rw [← hS]
      exact div_mul_cancel₀ _ hsub
    linear_combination h ζ * hSmul
  rw [e1, e2, ← add_div, hnum, mul_div_mul_left _ _ hP]

/-- Distribution of the remainder over the geometric sums. -/
private theorem wprep_remainder_distrib (d : ℕ) (b : Fin d → ℂ) (h : ℂ → ℂ)
    (ζ w : ℂ) :
    h ζ * (((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
        + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
          ζ ^ i * w ^ ((j : ℕ) - 1 - i)) /
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))
      = (∑ i ∈ Finset.range d, w ^ (d - 1 - i) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        + ∑ j : Fin d, ∑ i ∈ Finset.range (j : ℕ),
          (b j * w ^ ((j : ℕ) - 1 - i)) *
            (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) := by
  rw [← mul_div_assoc, mul_add, add_div]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- Integrability of the moment integrands. -/
private theorem wprep_moment_integrable
    (h : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hh : DifferentiableOn ℂ h (Metric.closedBall 0 ρ)) (d : ℕ) (b : Fin d → ℂ)
    (hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ) ≠ 0) :
    ∀ i : ℕ, CircleIntegrable
      (fun ζ => h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) 0 ρ := by
  intro i
  have hhcont : ContinuousOn h (Metric.sphere 0 ρ) :=
    hh.continuousOn.mono Metric.sphere_subset_closedBall
  have hAsum : Continuous fun ζ : ℂ => ∑ j : Fin d, b j * ζ ^ (j : ℕ) := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul (continuous_pow _)
  have hAcont : ContinuousOn
      (fun ζ : ℂ => ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
      (Metric.sphere 0 ρ) :=
    ((continuous_pow d).add hAsum).continuousOn
  have hdiv : CircleIntegrable
      (fun ζ : ℂ => h ζ / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) 0 ρ :=
    (hhcont.div hAcont (fun ζ hζ => hb ζ hζ)).circleIntegrable hρ.le
  have hpowc : ContinuousOn (fun ζ : ℂ => ζ ^ i) (Metric.sphere 0 |ρ|) := by
    rw [abs_of_nonneg hρ.le]
    exact (continuous_pow i).continuousOn.mono (Set.subset_univ _)
  have e : (fun ζ => h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))
      = (fun ζ => ζ ^ i) *
        (fun ζ => h ζ / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) := by
    funext ζ
    simp only [Pi.mul_apply]
    ring
  rw [e]
  exact CircleIntegrable.continuousOn_mul hdiv hpowc

/-- The remainder integral vanishes. -/
private theorem wprep_remainder_integral_eq_zero
    (h : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hh : DifferentiableOn ℂ h (Metric.closedBall 0 ρ)) (d : ℕ) (b : Fin d → ℂ)
    (hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ) ≠ 0)
    (hmom : ∀ i : ℕ, i < d →
      (∮ ζ in C((0 : ℂ), ρ), h ζ * ζ ^ i /
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) = 0)
    (w : ℂ) :
    (∮ ζ in C((0 : ℂ), ρ), h ζ *
        (((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
          + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
            ζ ^ i * w ^ ((j : ℕ) - 1 - i)) /
          (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) = 0 := by
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  have hint := wprep_moment_integrable h ρ hρ hh d b hb
  have hF : ∀ i : ℕ, CircleIntegrable
      (fun ζ => w ^ (d - 1 - i) *
        (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ := by
    intro i
    have hc : ContinuousOn (fun _ : ℂ => w ^ (d - 1 - i))
        (Metric.sphere 0 |ρ|) := by
      rw [abs_of_nonneg hρ.le]
      exact continuous_const.continuousOn
    exact CircleIntegrable.continuousOn_mul (hint i) hc
  have hG : ∀ (j : Fin d) (i : ℕ), CircleIntegrable
      (fun ζ => (b j * w ^ ((j : ℕ) - 1 - i)) *
        (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ := by
    intro j i
    have hc : ContinuousOn (fun _ : ℂ => b j * w ^ ((j : ℕ) - 1 - i))
        (Metric.sphere 0 |ρ|) := by
      rw [abs_of_nonneg hρ.le]
      exact continuous_const.continuousOn
    exact CircleIntegrable.continuousOn_mul (hint i) hc
  have hinner : ∀ j : Fin d, CircleIntegrable
      (∑ i ∈ Finset.range (j : ℕ), fun ζ : ℂ =>
        (b j * w ^ ((j : ℕ) - 1 - i)) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ :=
    fun j => CircleIntegrable.sum _ (fun i _ => hG j i)
  have hinnerL : ∀ j : Fin d, CircleIntegrable
      (fun ζ => ∑ i ∈ Finset.range (j : ℕ),
        (b j * w ^ ((j : ℕ) - 1 - i)) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ := by
    intro j
    have heq : Set.EqOn (∑ i ∈ Finset.range (j : ℕ), fun ζ : ℂ =>
        (b j * w ^ ((j : ℕ) - 1 - i)) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        (fun ζ => ∑ i ∈ Finset.range (j : ℕ),
          (b j * w ^ ((j : ℕ) - 1 - i)) *
            (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        (Metric.sphere 0 |ρ|) := by
      intro ζ _
      simp only [Finset.sum_apply]
    exact (circleIntegrable_congr heq).mp (hinner j)
  have hsum1 : CircleIntegrable
      (fun ζ => ∑ i ∈ Finset.range d, w ^ (d - 1 - i) *
        (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ := by
    have hbase : CircleIntegrable (∑ i ∈ Finset.range d, fun ζ : ℂ =>
        w ^ (d - 1 - i) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ :=
      CircleIntegrable.sum _ (fun i _ => hF i)
    have heq : Set.EqOn (∑ i ∈ Finset.range d, fun ζ : ℂ =>
        w ^ (d - 1 - i) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        (fun ζ => ∑ i ∈ Finset.range d, w ^ (d - 1 - i) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        (Metric.sphere 0 |ρ|) := by
      intro ζ _
      simp only [Finset.sum_apply]
    exact (circleIntegrable_congr heq).mp hbase
  have hsum2 : CircleIntegrable
      (fun ζ => ∑ j : Fin d, ∑ i ∈ Finset.range (j : ℕ),
        (b j * w ^ ((j : ℕ) - 1 - i)) *
          (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) 0 ρ := by
    have hbase : CircleIntegrable (∑ j : Fin d,
        (∑ i ∈ Finset.range (j : ℕ), fun ζ : ℂ =>
          (b j * w ^ ((j : ℕ) - 1 - i)) *
            (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))) 0 ρ :=
      CircleIntegrable.sum _ (fun j _ => hinner j)
    have heq : Set.EqOn (∑ j : Fin d,
        (∑ i ∈ Finset.range (j : ℕ), fun ζ : ℂ =>
          (b j * w ^ ((j : ℕ) - 1 - i)) *
            (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))))
        (fun ζ => ∑ j : Fin d, ∑ i ∈ Finset.range (j : ℕ),
          (b j * w ^ ((j : ℕ) - 1 - i)) *
            (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        (Metric.sphere 0 |ρ|) := by
      intro ζ _
      simp only [Finset.sum_apply]
    exact (circleIntegrable_congr heq).mp hbase
  rw [circleIntegral.integral_congr hρ0
    (fun ζ _ => wprep_remainder_distrib d b h ζ w),
    circleIntegral.integral_add hsum1 hsum2]
  have eS1 : (∮ ζ in C((0 : ℂ), ρ), ∑ i ∈ Finset.range d, w ^ (d - 1 - i) *
      (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) = 0 := by
    rw [circleIntegral.integral_fun_sum (fun i hi => hF i)]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [circleIntegral.integral_const_mul,
      hmom i (Finset.mem_range.mp hi), mul_zero]
  have eS2 : (∮ ζ in C((0 : ℂ), ρ), ∑ j : Fin d, ∑ i ∈ Finset.range (j : ℕ),
      (b j * w ^ ((j : ℕ) - 1 - i)) *
        (h ζ * ζ ^ i / (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))) = 0 := by
    rw [circleIntegral.integral_fun_sum (fun j _ => hinnerL j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [circleIntegral.integral_fun_sum (fun i _ => hG j i)]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [circleIntegral.integral_const_mul,
      hmom i (lt_trans (Finset.mem_range.mp hi) j.is_lt), mul_zero]
  rw [eS1, eS2, add_zero]

/-- One-variable division by a monic polynomial with vanishing moments. -/
private theorem wprep_eq_mul_circleIntegral_of_moments_eq_zero
    (h : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hh : DifferentiableOn ℂ h (Metric.closedBall 0 ρ)) (d : ℕ) (b : Fin d → ℂ)
    (hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ) ≠ 0)
    (hmom : ∀ i : ℕ, i < d →
      (∮ ζ in C((0 : ℂ), ρ), h ζ * ζ ^ i /
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) = 0)
    (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) ρ) :
    h w = (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) *
      ((2 * Real.pi * Complex.I)⁻¹ * ∮ ζ in C((0 : ℂ), ρ),
        h ζ / ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w))) := by
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  have hCauchy : (∮ ζ in C((0 : ℂ), ρ), (ζ - w)⁻¹ • h ζ)
      = (2 * Real.pi * Complex.I) • h w :=
    hh.circleIntegral_sub_inv_smul hw
  have hwnorm : ‖w‖ < ρ := by
    have h1 : dist w 0 < ρ := Metric.mem_ball.mp hw
    rwa [dist_zero_right] at h1
  have hζw : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ ≠ w := by
    intro ζ hζ hcon
    rw [mem_sphere_zero_iff_norm, hcon] at hζ
    linarith
  have hhcont : ContinuousOn h (Metric.sphere 0 ρ) :=
    hh.continuousOn.mono Metric.sphere_subset_closedBall
  have hAsum : Continuous fun ζ : ℂ => ∑ j : Fin d, b j * ζ ^ (j : ℕ) := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul (continuous_pow _)
  have hAcont : ContinuousOn
      (fun ζ : ℂ => ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
      (Metric.sphere 0 ρ) :=
    ((continuous_pow d).add hAsum).continuousOn
  have hsubc : ContinuousOn (fun ζ : ℂ => ζ - w) (Metric.sphere 0 ρ) :=
    (continuous_id.sub continuous_const).continuousOn
  have hQint : CircleIntegrable (fun ζ =>
      (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) *
        (h ζ / ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w)))) 0 ρ := by
    have hden : ContinuousOn
        (fun ζ : ℂ => (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w))
        (Metric.sphere 0 ρ) := hAcont.mul hsubc
    have hne : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w) ≠ 0 :=
      fun ζ hζ => mul_ne_zero (hb ζ hζ) (sub_ne_zero.mpr (hζw ζ hζ))
    have hcont : ContinuousOn (fun ζ : ℂ =>
        (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) *
          (h ζ / ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w))))
        (Metric.sphere 0 ρ) := by
      refine ContinuousOn.mul continuous_const.continuousOn ?_
      exact hhcont.div hden hne
    exact hcont.circleIntegrable hρ.le
  have hRint : CircleIntegrable (fun ζ => h ζ *
      (((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
        - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)) /
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) 0 ρ := by
    have hQcont : ContinuousOn (fun ζ : ℂ =>
        ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
          - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w))
        (Metric.sphere 0 ρ) := by
      refine ContinuousOn.div ?_ hsubc ?_
      · exact hAcont.sub continuous_const.continuousOn
      · exact fun ζ hζ => sub_ne_zero.mpr (hζw ζ hζ)
    have hcont : ContinuousOn (fun ζ : ℂ => h ζ *
        (((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
          - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)) /
          (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))
        (Metric.sphere 0 ρ) := by
      have hmul := hhcont.mul (hQcont.div hAcont (fun ζ hζ => hb ζ hζ))
      refine hmul.congr fun ζ _ => ?_
      rw [Pi.mul_apply, Pi.div_apply, mul_div_assoc]
    exact hcont.circleIntegrable hρ.le
  have hR := wprep_remainder_integral_eq_zero h ρ hρ hh d b hb hmom w
  have hR0 : (∮ ζ in C((0 : ℂ), ρ), h ζ *
      (((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
        - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)) /
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))) = 0 := by
    have hEq : Set.EqOn (fun ζ => h ζ *
        (((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
          - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)) /
          (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))
        (fun ζ => h ζ *
          (((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
            + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
              ζ ^ i * w ^ ((j : ℕ) - 1 - i)) /
            (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))))
        (Metric.sphere 0 ρ) := by
      intro ζ hζ
      change h ζ * (((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ))
        - (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ))) / (ζ - w)) /
        (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) = h ζ *
        (((∑ i ∈ Finset.range d, ζ ^ i * w ^ (d - 1 - i))
          + ∑ j : Fin d, b j * ∑ i ∈ Finset.range (j : ℕ),
            ζ ^ i * w ^ ((j : ℕ) - 1 - i)) /
          (ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)))
      rw [wprep_poly_div d b ζ w (hζw ζ hζ), mul_div_assoc]
    rw [circleIntegral.integral_congr hρ0 hEq]
    exact hR
  rw [circleIntegral.integral_congr hρ0
    (fun ζ hζ => wprep_split_integrand d b h ζ w (hb ζ hζ) (hζw ζ hζ)),
    circleIntegral.integral_add hQint hRint, hR0, add_zero,
    circleIntegral.integral_const_mul, smul_eq_mul] at hCauchy
  have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
  calc h w = (2 * Real.pi * Complex.I)⁻¹ * ((2 * Real.pi * Complex.I) * h w) :=
        (inv_mul_cancel_left₀ h2 _).symm
    _ = (w ^ d + ∑ j : Fin d, b j * w ^ (j : ℕ)) *
        ((2 * Real.pi * Complex.I)⁻¹ * ∮ ζ in C((0 : ℂ), ρ),
          h ζ / ((ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ)) * (ζ - w))) := by
        rw [← hCauchy]
        ring

/-- Choice of radii and setup facts. -/
private theorem wprep_setup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f (0 : E × ℂ))
    {d : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g (0 : ℂ))
    (h_order : ∀ᶠ w in 𝓝 (0 : ℂ), f ((0 : E), w) = w ^ d * g w) :
    ∃ r ρ : ℝ, 0 < ρ ∧ ρ < r ∧
      AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r) ∧
      DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ) ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ) ∧
      (∀ z : E, ‖z‖ < r →
        DifferentiableOn ℂ (fun ζ => f (z, ζ)) (Metric.closedBall (0 : ℂ) ρ)) := by
  obtain ⟨r, hr0, hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨rg, hrg0, hgr⟩ := hg.exists_ball_analyticOnNhd
  rw [Metric.eventually_nhds_iff] at h_order
  obtain ⟨ε, hε0, hε⟩ := h_order
  have hmin : 0 < min r (min rg ε) := lt_min hr0 (lt_min hrg0 hε0)
  set ρ := min r (min rg ε) / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρr : ρ < r := by rw [hρdef]; calc _ ≤ min r (min rg ε) / 2 := le_rfl
      _ < r := by linarith [min_le_left r (min rg ε), hmin]
  have hρrg : ρ < rg := by rw [hρdef]; calc _ ≤ min r (min rg ε) / 2 := le_rfl
      _ < rg := by linarith [min_le_right r (min rg ε), min_le_left rg ε, hmin]
  have hρε : ρ < ε := by rw [hρdef]; calc _ ≤ min r (min rg ε) / 2 := le_rfl
      _ < ε := by linarith [min_le_right r (min rg ε), min_le_right rg ε, hmin]
  refine ⟨r, ρ, hρ0, hρr, hfr, ?_, ?_, ?_⟩
  · -- `g` is differentiable on the closed ball of radius `ρ`
    have hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rg) := hgr.differentiableOn
    have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) rg := by
      intro ζ hζ
      rw [Metric.mem_ball]
      have hζ' : dist ζ 0 ≤ ρ := Metric.mem_closedBall.mp hζ
      calc dist ζ 0 ≤ ρ := hζ'
        _ < rg := hρrg
    exact hgd.mono hsub
  · -- the order hypothesis holds on the closed ball
    intro ζ hζ
    have hζ' : dist ζ 0 ≤ ρ := Metric.mem_closedBall.mp hζ
    have hmem : ζ ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball]
      calc dist ζ 0 ≤ ρ := hζ'
        _ < ε := hρε
    exact hε hmem
  · -- each slice is differentiable on the closed ball
    intro z hz
    have hpair : DifferentiableOn ℂ (fun ζ => (z, ζ)) (Metric.closedBall (0 : ℂ) ρ) :=
      (differentiableOn_const z).prodMk differentiableOn_id
    have hmaps : Set.MapsTo (fun ζ => (z, ζ)) (Metric.closedBall (0 : ℂ) ρ)
        (Metric.ball (0 : E × ℂ) r) := by
      intro ζ hζ
      change (z, ζ) ∈ Metric.ball (0 : E × ℂ) r
      have hζ' : dist ζ 0 ≤ ρ := Metric.mem_closedBall.mp hζ
      have hζn : ‖ζ‖ ≤ ρ := by simpa using hζ'
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      calc max ‖z‖ ‖ζ‖ ≤ max ‖z‖ ρ := by
            apply max_le_max le_rfl hζn
        _ < r := by
            rw [max_lt_iff]
            exact ⟨hz, hρr⟩
    exact (hfr.differentiableOn.comp hpair hmaps)

/-- The monic polynomial stays nonzero on the circle near `b = 0`. -/
private theorem wprep_monic_ne_zero_eventually
    (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ b in 𝓝 (0 : Fin d → ℂ), ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, b j * ζ ^ (j : ℕ) ≠ 0 := by
  have hcont : Continuous (fun p : (Fin d → ℂ) × ℂ =>
      p.2 ^ d + ∑ j : Fin d, p.1 j * p.2 ^ (j : ℕ)) := by
    refine Continuous.add ?_ (continuous_finsetSum _ fun j _ => ?_)
    · change Continuous ((Prod.snd : (Fin d → ℂ) × ℂ → ℂ) ^ d)
      exact continuous_snd.pow d
    · refine Continuous.mul ?_ ?_
      · exact (continuous_apply j).comp continuous_fst
      · change Continuous ((Prod.snd : (Fin d → ℂ) × ℂ → ℂ) ^ (j : ℕ))
        exact continuous_snd.pow (j : ℕ)
  have hne : ∀ ζ₀ ∈ Metric.sphere (0 : ℂ) ρ, ζ₀ ≠ 0 := by
    intro ζ₀ hζ₀ hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ₀
    linarith
  have hpt : ∀ ζ₀ ∈ Metric.sphere (0 : ℂ) ρ,
      ∀ᶠ p in 𝓝 ((0 : Fin d → ℂ), ζ₀),
        p.2 ^ d + ∑ j : Fin d, p.1 j * p.2 ^ (j : ℕ) ≠ 0 := by
    intro ζ₀ hζ₀
    have hval : ((0 : Fin d → ℂ), ζ₀).2 ^ d +
        ∑ j : Fin d, ((0 : Fin d → ℂ), ζ₀).1 j * ((0 : Fin d → ℂ), ζ₀).2 ^ (j : ℕ)
        ≠ 0 := by
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      exact pow_ne_zero _ (hne ζ₀ hζ₀)
    exact hcont.continuousAt.eventually_ne hval
  exact IsCompact.eventually_forall_of_forall_eventually (isCompact_sphere _ _) hpt

/-- Analyticity of the moment map. -/
private theorem wprep_analyticAt_moment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r)) :
    AnalyticAt ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) := by
  refine analyticAt_pi_iff.mpr fun m => ?_
  refine wprep_analyticAt_circleIntegral
    (fun p : (E × (Fin d → ℂ)) × ℂ => f (p.1.1, p.2) * p.2 ^ (m : ℕ) /
      (p.2 ^ d + ∑ j : Fin d, p.1.2 j * p.2 ^ (j : ℕ)))
    (0, 0) 0 ρ hρ ?_
  intro ζ₀ hζ₀
  have hζ0 : ζ₀ ≠ 0 := by
    intro hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ₀
    linarith
  have hnorm : ‖ζ₀‖ = ρ := mem_sphere_zero_iff_norm.mp hζ₀
  have hmem : ((0 : E), ζ₀) ∈ Metric.ball (0 : E × ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero,
      max_eq_right (norm_nonneg _), hnorm]
    exact hρr
  have hf_at : AnalyticAt ℂ f ((0 : E), ζ₀) := hfball _ hmem
  have hden : (ζ₀ ^ d + ∑ j : Fin d, ((0, 0) : E × (Fin d → ℂ)).2 j * ζ₀ ^ (j : ℕ))
      ≠ 0 := by
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    exact pow_ne_zero _ hζ0
  have hfst1 : AnalyticAt ℂ (fun p : (E × (Fin d → ℂ)) × ℂ => p.1.1) ((0, 0), ζ₀) :=
    analyticAt_fst.comp analyticAt_fst
  have hfst2 : AnalyticAt ℂ (fun p : (E × (Fin d → ℂ)) × ℂ => p.1.2) ((0, 0), ζ₀) :=
    analyticAt_snd.comp analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun p : (E × (Fin d → ℂ)) × ℂ => p.2) ((0, 0), ζ₀) :=
    analyticAt_snd
  have hcoord : ∀ j : Fin d, AnalyticAt ℂ
      (fun p : (E × (Fin d → ℂ)) × ℂ => p.1.2 j) ((0, 0), ζ₀) := by
    intro j
    exact ((ContinuousLinearMap.proj j).analyticAt _).comp hfst2
  fun_prop

/-- Analyticity of the quotient integral. -/
private theorem wprep_analyticAt_quotient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r)) :
    AnalyticAt ℂ (fun y : (E × (Fin d → ℂ)) × ℂ =>
      ∮ ζ in C((0 : ℂ), ρ), f (y.1.1, ζ) /
        ((ζ ^ d + ∑ j : Fin d, y.1.2 j * ζ ^ (j : ℕ)) * (ζ - y.2)))
      ((0, 0), 0) := by
  refine wprep_analyticAt_circleIntegral
    (fun p : ((E × (Fin d → ℂ)) × ℂ) × ℂ => f (p.1.1.1, p.2) /
      ((p.2 ^ d + ∑ j : Fin d, p.1.1.2 j * p.2 ^ (j : ℕ)) * (p.2 - p.1.2)))
    ((0, 0), 0) 0 ρ hρ ?_
  intro ζ₀ hζ₀
  have hζ0 : ζ₀ ≠ 0 := by
    intro hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ₀
    linarith
  have hnorm : ‖ζ₀‖ = ρ := mem_sphere_zero_iff_norm.mp hζ₀
  have hmem : ((0 : E), ζ₀) ∈ Metric.ball (0 : E × ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero,
      max_eq_right (norm_nonneg _), hnorm]
    exact hρr
  have hf_at : AnalyticAt ℂ f ((0 : E), ζ₀) := hfball _ hmem
  have hden : ((ζ₀ ^ d + ∑ j : Fin d, ((0, 0) : E × (Fin d → ℂ)).2 j * ζ₀ ^ (j : ℕ))
      * (ζ₀ - (((0, 0), 0) : (E × (Fin d → ℂ)) × ℂ).2)) ≠ 0 := by
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, sub_zero]
    exact mul_ne_zero (pow_ne_zero _ hζ0) hζ0
  have h111 : AnalyticAt ℂ (fun p : ((E × (Fin d → ℂ)) × ℂ) × ℂ => p.1.1.1)
      (((0, 0), 0), ζ₀) :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have h112 : AnalyticAt ℂ (fun p : ((E × (Fin d → ℂ)) × ℂ) × ℂ => p.1.1.2)
      (((0, 0), 0), ζ₀) :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have h12 : AnalyticAt ℂ (fun p : ((E × (Fin d → ℂ)) × ℂ) × ℂ => p.1.2)
      (((0, 0), 0), ζ₀) :=
    analyticAt_snd.comp analyticAt_fst
  have h2 : AnalyticAt ℂ (fun p : ((E × (Fin d → ℂ)) × ℂ) × ℂ => p.2)
      (((0, 0), 0), ζ₀) :=
    analyticAt_snd
  have hcoord : ∀ j : Fin d, AnalyticAt ℂ
      (fun p : ((E × (Fin d → ℂ)) × ℂ) × ℂ => p.1.1.2 j) (((0, 0), 0), ζ₀) := by
    intro j
    exact ((ContinuousLinearMap.proj j).analyticAt _).comp h112
  fun_prop

/-- Analyticity of the linearized moment map along a line. -/
private theorem wprep_analyticAt_moment_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r))
    (α : Fin d → ℂ) :
    AnalyticAt ℂ (fun t : ℂ => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (0, ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)))) 0 := by
  refine analyticAt_pi_iff.mpr fun m => ?_
  refine wprep_analyticAt_circleIntegral
    (fun q : ℂ × ℂ => f (0, q.2) * q.2 ^ (m : ℕ) *
      (∑ j : Fin d, α j * q.2 ^ (j : ℕ)) /
      (q.2 ^ d * (q.2 ^ d + ∑ j : Fin d, (q.1 • α) j * q.2 ^ (j : ℕ))))
    0 0 ρ hρ ?_
  intro ζ₀ hζ₀
  have hζ0 : ζ₀ ≠ 0 := by
    intro hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ₀
    linarith
  have hnorm : ‖ζ₀‖ = ρ := mem_sphere_zero_iff_norm.mp hζ₀
  have hmem : ((0 : E), ζ₀) ∈ Metric.ball (0 : E × ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero,
      max_eq_right (norm_nonneg _), hnorm]
    exact hρr
  have hf_at : AnalyticAt ℂ f ((0 : E), ζ₀) := hfball _ hmem
  have hden : (ζ₀ ^ d * (ζ₀ ^ d + ∑ j : Fin d, ((0 : ℂ) • α) j * ζ₀ ^ (j : ℕ)))
      ≠ 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, zero_mul, Finset.sum_const_zero, add_zero]
    exact mul_ne_zero (pow_ne_zero _ hζ0) (pow_ne_zero _ hζ0)
  have h1 : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) (0, ζ₀) := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) (0, ζ₀) := analyticAt_snd
  have hsmul : ∀ j : Fin d, AnalyticAt ℂ
      (fun q : ℂ × ℂ => (q.1 • α) j) (0, ζ₀) := by
    intro j
    have e : (fun q : ℂ × ℂ => (q.1 • α) j) = (fun q : ℂ × ℂ => q.1 • α j) := by
      funext q
      exact Pi.smul_apply _ _ _
    rw [e]
    exact analyticAt_fst.smul analyticAt_const
  fun_prop

/-- Base values of the moments vanish. -/
private theorem wprep_moment_base_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ) :
    (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) = 0 := by
  funext m
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have hEq : Set.EqOn (fun ζ => f (0, ζ) * ζ ^ (m : ℕ) / ζ ^ d)
      (fun ζ => g ζ * ζ ^ (d + (m : ℕ)) / ζ ^ d)
      (Metric.sphere (0 : ℂ) ρ) := by
    intro ζ hζ
    have hmem : ζ ∈ Metric.closedBall (0 : ℂ) ρ :=
      Metric.sphere_subset_closedBall hζ
    change f (0, ζ) * ζ ^ (m : ℕ) / ζ ^ d = g ζ * ζ ^ (d + (m : ℕ)) / ζ ^ d
    rw [hfg ζ hmem]
    ring
  rw [circleIntegral.integral_congr hρ0 hEq]
  exact wprep_circleIntegral_pow_ratio_eq_zero g ρ hρ hg d (d + (m : ℕ))
    (Nat.le_add_right _ _)

/-- Base value of the quotient integral. -/
private theorem wprep_quotient_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ) :
    (2 * Real.pi * Complex.I)⁻¹ * (∮ ζ in C((0 : ℂ), ρ), f (0, ζ) /
      ((ζ ^ d + ∑ j : Fin d, ((0 : E × (Fin d → ℂ)).2) j * ζ ^ (j : ℕ)) *
        (ζ - 0))) = g 0 := by
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  simp only [Prod.snd_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    sub_zero]
  have hEq : Set.EqOn (fun ζ => f (0, ζ) / (ζ ^ d * ζ))
      (fun ζ => g ζ * ζ ^ 0 / ζ ^ 1)
      (Metric.sphere (0 : ℂ) ρ) := by
    intro ζ hζ
    have hmem : ζ ∈ Metric.closedBall (0 : ℂ) ρ :=
      Metric.sphere_subset_closedBall hζ
    have hζ0 : ζ ≠ 0 := by
      intro hcon
      rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
      linarith
    have hpow : ζ ^ d ≠ 0 := pow_ne_zero _ hζ0
    change f (0, ζ) / (ζ ^ d * ζ) = g ζ * ζ ^ 0 / ζ ^ 1
    rw [hfg ζ hmem]
    field_simp
  rw [circleIntegral.integral_congr hρ0 hEq,
    wprep_circleIntegral_pow_ratio_eq_two_pi_I g ρ hρ hg 1 0 rfl,
    inv_mul_cancel_left₀ Complex.two_pi_I_ne_zero]

/-- Each central slice of `f` is differentiable on the closed disc. -/
private theorem wprep_slice_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {r ρ : ℝ} (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r)) :
    DifferentiableOn ℂ (fun ζ : ℂ => f ((0 : E), ζ))
      (Metric.closedBall (0 : ℂ) ρ) := by
  have hpair : DifferentiableOn ℂ (fun ζ : ℂ => ((0 : E), ζ))
      (Metric.closedBall (0 : ℂ) ρ) :=
    (differentiableOn_const (0 : E)).prodMk differentiableOn_id
  have hmaps : Set.MapsTo (fun ζ : ℂ => ((0 : E), ζ))
      (Metric.closedBall (0 : ℂ) ρ) (Metric.ball (0 : E × ℂ) r) := by
    intro ζ hζ
    have hζn : ‖ζ‖ ≤ ρ := by
      have h1 : dist ζ 0 ≤ ρ := Metric.mem_closedBall.mp hζ
      simpa using h1
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk, norm_zero,
      max_eq_right (norm_nonneg _)]
    exact lt_of_le_of_lt hζn hρr
  exact hfball.differentiableOn.comp hpair hmaps

/-- Coordinate form of the vanishing base moments. -/
private theorem wprep_moment_base_zero_coord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ)
    (m : Fin d) :
    (∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) / ζ ^ d) = 0 := by
  have hbase := wprep_moment_base_zero (E := E) hρ hg hfg (f := f) (d := d)
  have hm := congrFun hbase m
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at hm
  exact hm

/-- Pointwise polynomial identity for the moment difference. -/
private theorem wprep_moment_pointwise
    (d : ℕ) (α : Fin d → ℂ) (t ζ : ℂ)
    (hζ : ζ ^ d ≠ 0)
    (hP : ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ) ≠ 0)
    (a : ℂ) (m : ℕ) :
    a * ζ ^ m / (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)) - a * ζ ^ m / ζ ^ d
      = (-t) * (a * ζ ^ m * (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)))) := by
  have hPs : ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)
      = ζ ^ d + t * ∑ j : Fin d, α j * ζ ^ (j : ℕ) := by
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [hPs] at hP ⊢
  field_simp
  ring

/-- Value of the linearized map at `t = 0`. -/
private theorem wprep_moment_line_value_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ)
    (α : Fin d → ℂ) (m : Fin d) :
    (∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, ((0 : ℂ) • α) j * ζ ^ (j : ℕ))))
      = ∑ j : Fin d, α j *
        (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d) := by
  have hb0 : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, (0 : Fin d → ℂ) j * ζ ^ (j : ℕ) ≠ 0 := by
    intro ζ hζ
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    apply pow_ne_zero _ _
    intro hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
    linarith
  have hint : ∀ j : Fin d, CircleIntegrable
      (fun ζ => α j * (g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d)) 0 ρ := by
    intro j
    have hmj := wprep_moment_integrable g ρ hρ hg d 0 hb0 ((m : ℕ) + (j : ℕ))
    have hmj' : CircleIntegrable
        (fun ζ => g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d) 0 ρ := by
      simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        add_zero] using hmj
    have hc : ContinuousOn (fun _ : ℂ => α j) (Metric.sphere 0 |ρ|) :=
      continuous_const.continuousOn
    have hmj2 := CircleIntegrable.continuousOn_mul hmj' hc
    have heq : Set.EqOn ((fun _ : ℂ => α j) *
        (fun ζ => g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d))
        (fun ζ => α j * (g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d))
        (Metric.sphere 0 |ρ|) := by
      intro ζ _
      simp only [Pi.mul_apply]
    exact (circleIntegrable_congr heq).mp hmj2
  have hterm : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, ((0 : ℂ) • α) j * ζ ^ (j : ℕ)))
      = ∑ j : Fin d, α j * (g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d) := by
    intro ζ hζ
    have hmem : ζ ∈ Metric.closedBall (0 : ℂ) ρ :=
      Metric.sphere_subset_closedBall hζ
    have hζd : ζ ^ d ≠ 0 := by
      apply pow_ne_zero _ _
      intro hcon
      rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
      linarith
    have hP0 : ζ ^ d + ∑ j : Fin d, ((0 : ℂ) • α) j * ζ ^ (j : ℕ) = ζ ^ d := by
      simp only [Pi.smul_apply, smul_eq_mul, zero_mul, Finset.sum_const_zero,
        add_zero]
    rw [hP0, hfg ζ hmem, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    field_simp
  have hEq : Set.EqOn
      (fun ζ => f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, ((0 : ℂ) • α) j * ζ ^ (j : ℕ))))
      (fun ζ => ∑ j : Fin d, α j * (g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d))
      (Metric.sphere (0 : ℂ) ρ) := hterm
  rw [circleIntegral.integral_congr hρ.le hEq,
    circleIntegral.integral_fun_sum (fun j _ => hint j)]
  exact Finset.sum_congr rfl fun j _ =>
    circleIntegral.integral_const_mul _ _ _ _

/-- The moment line equals a scalar multiple of the linearized map near `t = 0`. -/
private theorem wprep_moment_line_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r))
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ)
    (α : Fin d → ℂ) :
    (fun t : ℂ => (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) ((0 : E), t • α))
      =ᶠ[𝓝 (0 : ℂ)] ((fun t : ℂ => -t) • (fun t : ℂ => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ))))) := by
  have hlim : Filter.Tendsto (fun t : ℂ => t • α) (𝓝 (0 : ℂ))
      (𝓝 (0 : Fin d → ℂ)) := by
    have hca : ContinuousAt (fun t : ℂ => t • α) (0 : ℂ) :=
      (continuous_id.smul continuous_const).continuousAt
    have h1 : Filter.Tendsto (fun t : ℂ => t • α) (𝓝 (0 : ℂ))
        (𝓝 ((0 : ℂ) • α)) := hca.tendsto
    rwa [zero_smul] at h1
  have hslice := wprep_slice_differentiableOn (E := E) hρr hfball (f := f)
  filter_upwards [hlim.eventually (wprep_monic_ne_zero_eventually d ρ hρ)]
    with t ht
  funext m
  have hb0 : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, (0 : Fin d → ℂ) j * ζ ^ (j : ℕ) ≠ 0 := by
    intro ζ hζ
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    apply pow_ne_zero _ _
    intro hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
    linarith
  have hA : CircleIntegrable
      (fun ζ => f ((0 : E), ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ))) 0 ρ :=
    wprep_moment_integrable _ ρ hρ hslice d (t • α) ht m
  have hB : CircleIntegrable
      (fun ζ => f ((0 : E), ζ) * ζ ^ (m : ℕ) / ζ ^ d) 0 ρ := by
    have hB' := wprep_moment_integrable (fun ζ => f ((0 : E), ζ)) ρ hρ hslice
      d 0 hb0 m
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero] using hB'
  have h0m := wprep_moment_base_zero_coord (E := E) hρ hg hfg (f := f) m
  have hsub := circleIntegral.integral_sub hA hB
  rw [h0m, sub_zero] at hsub
  change (∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) /
      (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)))
    = (-t) • (∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ))))
  rw [smul_eq_mul, ← circleIntegral.integral_const_mul, ← hsub]
  apply circleIntegral.integral_congr hρ.le
  intro ζ hζ
  have hζd : ζ ^ d ≠ 0 := by
    apply pow_ne_zero _ _
    intro hcon
    rw [mem_sphere_zero_iff_norm, hcon, norm_zero] at hζ
    linarith
  exact wprep_moment_pointwise d α t ζ hζd (ht ζ hζ) _ _

/-- Derivative of the moment map along a line through the base point. -/
private theorem wprep_hasDerivAt_moment_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r))
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ)
    (α : Fin d → ℂ) :
    HasDerivAt (fun t : ℂ => (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) ((0 : E), t • α))
      (fun m : Fin d => -∑ j : Fin d, α j *
        (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d)) 0 := by
  have hN : AnalyticAt ℂ (fun t : ℂ => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)))) 0 :=
    wprep_analyticAt_moment_line hρ hρr hfball α
  have hNder := hN.differentiableAt.hasDerivAt
  have hscalar : HasDerivAt (fun t : ℂ => -t) (-1 : ℂ) (0 : ℂ) := by
    have h := (hasDerivAt_id (0 : ℂ)).neg
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    rfl
  have hsmul := hscalar.smul hNder
  have hEq := wprep_moment_line_eventuallyEq hρ hρr hfball hg hfg α
  simp only [neg_zero] at hsmul
  have e1 : (0 : ℂ) • deriv (fun t : ℂ => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)))) 0 = 0 := by
    simp
  rw [e1, zero_add] at hsmul
  have hderiv : ((-1 : ℂ) • ((fun t : ℂ => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, (t • α) j * ζ ^ (j : ℕ)))) 0))
      = (fun m : Fin d => -∑ j : Fin d, α j *
        (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d)) := by
    funext m
    change (-1 : ℂ) • (∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) * ζ ^ (m : ℕ) *
        (∑ j : Fin d, α j * ζ ^ (j : ℕ)) /
        (ζ ^ d * (ζ ^ d + ∑ j : Fin d, ((0 : ℂ) • α) j * ζ ^ (j : ℕ)))) = _
    rw [wprep_moment_line_value_zero (E := E) hρ hg hfg (f := f) α m]
    simp
  rw [hderiv] at hsmul
  exact hsmul.congr_of_eventuallyEq hEq

/-- Formula for the Jacobian applied to a vector. -/
private theorem wprep_jacobian_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r))
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ)
    (α : Fin d → ℂ) :
    ((fderiv ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) ∘L
      ContinuousLinearMap.inr ℂ E (Fin d → ℂ)) α)
      = (fun m : Fin d => -∑ j : Fin d, α j *
        (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d)) := by
  have hG : AnalyticAt ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) :=
    wprep_analyticAt_moment hρ hρr hfball
  have hGfd := hG.differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun t : ℂ => ((0 : E), t • α))
      ((ContinuousLinearMap.inr ℂ E (Fin d → ℂ)) α) 0 := by
    have hbase : HasDerivAt (fun y : ℂ => id y • ((0 : E), α))
        ((1 : ℂ) • ((0 : E), α)) 0 :=
      (hasDerivAt_id (0 : ℂ)).smul_const _
    have hval : ((1 : ℂ) • ((0 : E), (α : Fin d → ℂ)))
        = (ContinuousLinearMap.inr ℂ E (Fin d → ℂ)) α := by
      simp
    rw [hval] at hbase
    refine hbase.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp
  have hy : ((0 : E), (0 : Fin d → ℂ)) = ((0 : E), (0 : ℂ) • α) :=
    Prod.ext rfl (by simp)
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (hl := hGfd) (hf := hline)
    (hy := hy)
  have hfun : ((fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) ∘
      (fun t : ℂ => ((0 : E), t • α)))
      =ᶠ[𝓝 (0 : ℂ)] (fun t : ℂ => (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) ((0 : E), t • α)) :=
    Filter.Eventually.of_forall fun t => rfl
  have hcomp2 := hcomp.congr_of_eventuallyEq hfun
  have hN11 := wprep_hasDerivAt_moment_line hρ hρr hfball hg hfg α
  have heq := hcomp2.unique hN11
  rw [ContinuousLinearMap.comp_apply]
  exact heq

/-- Injectivity of an anti-triangular moment matrix. -/
private theorem wprep_jacobian_injective
    {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hg0 : g (0 : ℂ) ≠ 0)
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (hform : ∀ α : Fin d → ℂ, L α = fun m : Fin d => -∑ j : Fin d, α j *
      (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d)) :
    Function.Injective L := by
  intro α β hab
  have hsub : L (α - β) = 0 := by
    rw [map_sub, hab, sub_self]
  have hcoord : ∀ m : Fin d, ∑ j : Fin d, (α - β) j *
      (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d) = 0 := by
    intro m
    have hm := congrFun hsub m
    rw [hform (α - β)] at hm
    simpa only [Pi.zero_apply, neg_eq_zero] using hm
  have hc_ge : ∀ k : ℕ, d ≤ k →
      (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ k / ζ ^ d) = 0 :=
    fun k hk => wprep_circleIntegral_pow_ratio_eq_zero g ρ hρ hg d k hk
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · funext j
    exact Fin.elim0 j
  · have hc_sub : (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ (d - 1) / ζ ^ d)
        = 2 * Real.pi * Complex.I * g 0 :=
      wprep_circleIntegral_pow_ratio_eq_two_pi_I g ρ hρ hg d (d - 1) (by omega)
    have hc0 : 2 * Real.pi * Complex.I * g (0 : ℂ) ≠ 0 :=
      mul_ne_zero Complex.two_pi_I_ne_zero hg0
    have key : ∀ n : ℕ, ∀ j : Fin d, (j : ℕ) = n → (α - β) j = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro j hj
        have hmj : ((Fin.rev j : Fin d) : ℕ) = d - ((j : ℕ) + 1) :=
          Fin.val_rev _
        have hmsum : ((Fin.rev j : Fin d) : ℕ) + (j : ℕ) = d - 1 := by
          omega
        have hrow := hcoord (Fin.rev j)
        have h0 : ∀ i ∈ Finset.univ, i ≠ j → (α - β) i *
            (∮ ζ in C((0 : ℂ), ρ),
              g ζ * ζ ^ (((Fin.rev j : Fin d) : ℕ) + (i : ℕ)) / ζ ^ d) = 0 := by
          intro i _ hii
          by_cases hlt : (i : ℕ) < (j : ℕ)
          · have hi0 := ih _ (lt_of_lt_of_le hlt hj.le) i rfl
            rw [hi0, zero_mul]
          · have hji : (j : ℕ) < (i : ℕ) := by
              have hne : (i : ℕ) ≠ (j : ℕ) :=
                fun h => hii (Fin.val_injective h)
              omega
            have hge : d ≤ ((Fin.rev j : Fin d) : ℕ) + (i : ℕ) := by
              omega
            rw [hc_ge _ hge, mul_zero]
        rw [Finset.sum_eq_single j h0 (by simp)] at hrow
        rw [hmsum, hc_sub] at hrow
        exact (mul_eq_zero.mp hrow).resolve_right hc0
    have h0 : α - β = 0 := by
      funext j
      exact key _ j rfl
    exact sub_eq_zero.mp h0

/-- Invertibility of the partial Jacobian in the `b` variable. -/
private theorem wprep_jacobian_isInvertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {d : ℕ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r))
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hg0 : g (0 : ℂ) ≠ 0)
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ) :
    (fderiv ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) ∘L
      ContinuousLinearMap.inr ℂ E (Fin d → ℂ)).IsInvertible := by
  have hform : ∀ α : Fin d → ℂ,
      ((fderiv ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
        ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
          (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) ∘L
        ContinuousLinearMap.inr ℂ E (Fin d → ℂ)) α)
        = (fun m : Fin d => -∑ j : Fin d, α j *
          (∮ ζ in C((0 : ℂ), ρ), g ζ * ζ ^ ((m : ℕ) + (j : ℕ)) / ζ ^ d)) :=
    fun α => wprep_jacobian_apply hρ hρr hfball hg hfg α
  have hinj : Function.Injective
      ((fderiv ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
        ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
          (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) ∘L
        ContinuousLinearMap.inr ℂ E (Fin d → ℂ))) :=
    wprep_jacobian_injective hρ hg hg0 _ hform
  have hinj' : Function.Injective
      (((fderiv ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
        ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
          (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) ∘L
        ContinuousLinearMap.inr ℂ E (Fin d → ℂ)) :
        (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))) := hinj
  refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj').toContinuousLinearEquiv, ?_⟩
  ext x
  simp only [ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.coe_ofInjectiveEndo, ContinuousLinearMap.coe_coe]

/-- The implicit coefficient map. -/
private theorem wprep_implicit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ}
    {d : ℕ} {g : ℂ → ℂ} (hg0 : g (0 : ℂ) ≠ 0)
    {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hfball : AnalyticOnNhd ℂ f (Metric.ball (0 : E × ℂ) r))
    (hgball : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ρ))
    (hfg : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ρ, f ((0 : E), ζ) = ζ ^ d * g ζ) :
    ∃ ψ : E → (Fin d → ℂ), ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧
      ∀ᶠ z in 𝓝 (0 : E),
        (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
          ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
            (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (z, ψ z) = 0 := by
  have := FiniteDimensional.complete ℂ E
  have hG : AnalyticAt ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) :=
    wprep_analyticAt_moment hρ hρr hfball
  have hGc : ContDiffAt ℂ ω (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) :=
    hG.contDiffAt
  have hJ : (fderiv ℂ (fun x : E × (Fin d → ℂ) => fun m : Fin d =>
      ∮ ζ in C((0 : ℂ), ρ), f (x.1, ζ) * ζ ^ (m : ℕ) /
        (ζ ^ d + ∑ j : Fin d, x.2 j * ζ ^ (j : ℕ))) (0, 0) ∘L
      ContinuousLinearMap.inr ℂ E (Fin d → ℂ)).IsInvertible :=
    wprep_jacobian_isInvertible hρ hρr hfball hgball hg0 hfg
  refine ⟨hGc.implicitFunction (by simp) hJ, ?_, ?_, ?_⟩
  · exact hGc.implicitFunction_apply_self (by simp) hJ
  · exact (hGc.contDiffAt_implicitFunction (by simp) hJ).analyticAt
  · have hev := hGc.eventually_apply_implicitFunction (by simp) hJ
    have hbase := wprep_moment_base_zero (E := E) hρ hgball hfg (f := f)
      (d := d)
    filter_upwards [hev] with z hz
    rw [hz]
    exact hbase

/--
**Weierstrass preparation theorem.** Let $E$ be a finite-dimensional normed vector space over
$\mathbb{C}$ and let $f : E \times \mathbb{C} \to \mathbb{C}$ be analytic at $0$. Suppose that for
some $d \in \mathbb{N}$ and some $g : \mathbb{C} \to \mathbb{C}$ analytic at $0$ with $g(0) \ne 0$,
$f(0, w) = w^d g(w)$ for all $w$ in a neighbourhood of $0$. Then there are functions
$a_0, \dots, a_{d-1} : E \to \mathbb{C}$, each analytic at $0$ with $a_j(0) = 0$, a function
$u : E \times \mathbb{C} \to \mathbb{C}$ analytic at $0$ with $u(0) \ne 0$, and an open set
$U \subseteq E \times \mathbb{C}$ containing $0$ such that
$f(z, w) = u(z, w) \bigl(w^d + \sum_{j=0}^{d-1} a_j(z) w^j\bigr)$ for all $(z, w) \in U$.

Source: Weierstrass
preparation theorem in several complex variables; see Hörmander; Lean is finite-dimensional E × ℂ
product form, order d slice factorization w^d g w, Weierstrass polynomial with vanishing
coefficients and unit u, local open U, fixed field ℂ specialization.

Proves `Wanted` entry `weierstrass_preparation`.
-/
public theorem weierstrass_preparation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} (hf : AnalyticAt ℂ f (0 : E × ℂ))
    {d : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g (0 : ℂ)) (hg0 : g (0 : ℂ) ≠ 0)
    (h_order : ∀ᶠ w in 𝓝 (0 : ℂ), f ((0 : E), w) = w ^ d * g w) :
    ∃ (a : Fin d → E → ℂ) (u : E × ℂ → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (0 : E)) ∧
      (∀ j, a j (0 : E) = 0) ∧
      AnalyticAt ℂ u (0 : E × ℂ) ∧ u (0 : E × ℂ) ≠ 0 ∧
      ∃ U : Set (E × ℂ), IsOpen U ∧ (0 : E × ℂ) ∈ U ∧
        ∀ p ∈ U, f p = u p * (p.2 ^ d + ∑ j : Fin d, a j p.1 * p.2 ^ (j : ℕ)) := by
  obtain ⟨r, ρ, hρ, hρr, hfball, hgball, hfg, hslice⟩ :=
    wprep_setup hf hg h_order
  obtain ⟨ψ, hψ0, hψan, hψvan⟩ :=
    wprep_implicit hg0 hρ hρr hfball hgball hfg
  have hψcont : ContinuousAt ψ (0 : E) := hψan.continuousAt
  have hlim : Filter.Tendsto ψ (𝓝 (0 : E)) (𝓝 (0 : Fin d → ℂ)) := by
    have h1 : Filter.Tendsto ψ (𝓝 (0 : E)) (𝓝 (ψ (0 : E))) :=
      hψcont.tendsto
    rwa [hψ0] at h1
  have hnonvan : ∀ᶠ z in 𝓝 (0 : E), ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ,
      ζ ^ d + ∑ j : Fin d, ψ z j * ζ ^ (j : ℕ) ≠ 0 :=
    hlim.eventually (wprep_monic_ne_zero_eventually d ρ hρ)
  have hr0 : 0 < r := lt_trans hρ hρr
  have hball : ∀ᶠ z in 𝓝 (0 : E), ‖z‖ < r := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr0] with z hz
    simpa using hz
  have hcomb := hψvan.and (hnonvan.and hball)
  rw [Metric.eventually_nhds_iff] at hcomb
  obtain ⟨δ, hδ0, hδ⟩ := hcomb
  have hQ : AnalyticAt ℂ (fun y : (E × (Fin d → ℂ)) × ℂ =>
      ∮ ζ in C((0 : ℂ), ρ), f (y.1.1, ζ) /
        ((ζ ^ d + ∑ j : Fin d, y.1.2 j * ζ ^ (j : ℕ)) * (ζ - y.2)))
      ((0, 0), 0) :=
    wprep_analyticAt_quotient hρ hρr hfball
  have hψfst : AnalyticAt ℂ (ψ ∘ fun p : E × ℂ => p.1) (0 : E × ℂ) :=
    AnalyticAt.comp (g := ψ) (f := fun p : E × ℂ => p.1) (x := (0 : E × ℂ))
      hψan analyticAt_fst
  have hΦraw := (analyticAt_fst.prod hψfst).prod analyticAt_snd
  have hΦ : AnalyticAt ℂ (fun p : E × ℂ => ((p.1, ψ p.1), p.2))
      (0 : E × ℂ) := by
    refine hΦraw.congr (Filter.Eventually.of_forall fun p => ?_)
    rfl
  have hΦ0 : ((fun p : E × ℂ => ((p.1, ψ p.1), p.2)) (0 : E × ℂ))
      = ((0, 0), 0) := by
    simp [hψ0]
  have hQu : AnalyticAt ℂ ((fun y : (E × (Fin d → ℂ)) × ℂ =>
      ∮ ζ in C((0 : ℂ), ρ), f (y.1.1, ζ) /
        ((ζ ^ d + ∑ j : Fin d, y.1.2 j * ζ ^ (j : ℕ)) * (ζ - y.2))) ∘
      (fun p : E × ℂ => ((p.1, ψ p.1), p.2))) (0 : E × ℂ) :=
    hQ.comp_of_eq hΦ hΦ0
  have hu_an : AnalyticAt ℂ (fun p : E × ℂ =>
      (2 * Real.pi * Complex.I)⁻¹ *
        (∮ ζ in C((0 : ℂ), ρ), f (p.1, ζ) /
          ((ζ ^ d + ∑ j : Fin d, ψ p.1 j * ζ ^ (j : ℕ)) * (ζ - p.2))))
      (0 : E × ℂ) := by
    have hconst : AnalyticAt ℂ (fun _ : E × ℂ => (2 * Real.pi * Complex.I)⁻¹)
        (0 : E × ℂ) := analyticAt_const
    have hmul := hconst.mul hQu
    refine hmul.congr (Filter.Eventually.of_forall fun p => ?_)
    rfl
  have hu0val : (2 * Real.pi * Complex.I)⁻¹ *
      (∮ ζ in C((0 : ℂ), ρ), f ((0 : E), ζ) /
        ((ζ ^ d + ∑ j : Fin d, ψ (0 : E) j * ζ ^ (j : ℕ)) * (ζ - (0 : ℂ))))
      = g (0 : ℂ) := by
    have hbase := wprep_quotient_base (E := E) hρ hgball hfg (f := f) (d := d)
    rw [hψ0]
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
      Prod.snd_zero] using hbase
  refine ⟨fun j z => ψ z j,
    fun p => (2 * Real.pi * Complex.I)⁻¹ *
      (∮ ζ in C((0 : ℂ), ρ), f (p.1, ζ) /
        ((ζ ^ d + ∑ j : Fin d, ψ p.1 j * ζ ^ (j : ℕ)) * (ζ - p.2))),
    fun j => analyticAt_pi_iff.mp hψan j,
    fun j => by simp [hψ0],
    hu_an, ?_, Metric.ball (0 : E) δ ×ˢ Metric.ball (0 : ℂ) ρ, ?_, ?_, ?_⟩
  · -- `u 0 = g 0 ≠ 0`
    have hu0 : (fun p : E × ℂ => (2 * Real.pi * Complex.I)⁻¹ *
        (∮ ζ in C((0 : ℂ), ρ), f (p.1, ζ) /
          ((ζ ^ d + ∑ j : Fin d, ψ p.1 j * ζ ^ (j : ℕ)) * (ζ - p.2))))
        (0 : E × ℂ) ≠ 0 := by
      have e := hu0val
      simp only [Prod.fst_zero, Prod.snd_zero] at e ⊢
      rw [e]
      exact hg0
    exact hu0
  · exact IsOpen.prod Metric.isOpen_ball Metric.isOpen_ball
  · exact ⟨Metric.mem_ball_self hδ0, Metric.mem_ball_self hρ⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have h1 : ‖p.1‖ < δ := by
      rwa [Metric.mem_ball, dist_zero_right] at hp1
    have hzδ : p.1 ∈ Metric.ball (0 : E) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact h1
    obtain ⟨hi, hii, hiii⟩ := hδ hzδ
    have hmom : ∀ i : ℕ, i < d →
        (∮ ζ in C((0 : ℂ), ρ), f (p.1, ζ) * ζ ^ i /
          (ζ ^ d + ∑ j : Fin d, ψ p.1 j * ζ ^ (j : ℕ))) = 0 := by
      intro i hii2
      have hm := congrFun hi ⟨i, hii2⟩
      simpa using hm
    have hfac := wprep_eq_mul_circleIntegral_of_moments_eq_zero
      (fun ζ => f (p.1, ζ)) ρ hρ (hslice p.1 hiii) d (ψ p.1) hii hmom p.2 hp2
    have hp12 : p = (p.1, p.2) := Prod.mk.eta.symm
    rw [hp12, mul_comm]
    exact hfac

end MathlibExt.Analysis.Complex.WeierstrassPreparationWanted
