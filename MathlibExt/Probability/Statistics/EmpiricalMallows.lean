/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Measure.Portmanteau
import MathlibExt.MeasureTheory.OptimalTransport.WassersteinConvergence

/-!
# Almost sure convergence of the empirical law in the Mallows metric

For `1 ≤ p`, the empirical laws of an i.i.d. sequence with finite `p`-th moment converge
almost surely to the common law in Wasserstein distance (`tendsto_wasserstein_empirical`).
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open MathlibExt.MeasureTheory.WassersteinWanted (tendsto_wasserstein_iff)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.Probability.Statistics.BootstrapWanted

/-- The strong law applied to the integral of a single test function against the empirical law. -/
private theorem empirical_integral_tendsto {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] {P : Measure Ω} {X : ℕ → Ω → E}
    (hX : Measurable (X 0)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (μ : ProbabilityMeasure E)
    (hlaw : P.map (X 0) = (μ : Measure E)) (F : ℕ → Ω → ProbabilityMeasure E)
    (hF : ∀ n ω, (F n ω : Measure E) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range (n + 1), Measure.dirac (X i ω))
    (g : E → ℝ) (hg : Measurable g) (hgi : Integrable g (μ : Measure E)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, g x ∂(F n ω : Measure E)) atTop
      (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
  rw [← hlaw] at hgi ⊢
  rw [integral_map hX.aemeasurable hg.aestronglyMeasurable]
  have H := strong_law_ae_real (fun i => g ∘ X i)
    ((integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).mp hgi)
    (fun i j hij => (hindep.indepFun hij).comp hg hg) (fun i => (hident i).comp hg)
  filter_upwards [H] with ω hω
  refine (hω.comp (tendsto_add_atTop_nat 1)).congr (fun n => ?_)
  rw [hF, integral_smul_measure, integral_finsetSum_measure
    (fun i _ => integrable_dirac (f := g) (a := X i ω) (by finiteness))]
  simp [div_eq_inv_mul, ENNReal.toReal_add]

/-- Finite intersections of basic open sets give a countable convergence-determining class. -/
private theorem empirical_weak_tendsto {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [TopologicalSpace E] [SecondCountableTopology E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (F : ℕ → Ω → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (h : ∀ s : Set E, MeasurableSet s →
      ∀ᵐ ω ∂P, Tendsto (fun n => F n ω s) atTop (𝓝 (μ s))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 μ) := by
  classical
  obtain ⟨B, hcount, -, hB⟩ := TopologicalSpace.exists_countable_basis E
  let := hcount.to_subtype
  let cell (t : Finset B) : Set E := ⋂ s ∈ t, (s : Set E)
  have hcell (t : Finset B) : MeasurableSet (cell t) :=
    t.measurableSet_biInter fun s _ => (hB.isOpen s.property).measurableSet
  have hpi : IsPiSystem (Set.range cell) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
    refine ⟨s ∪ t, ?_⟩
    change (⋂ i ∈ (↑(s ∪ t) : Set B), (i : Set E)) = _
    rw [Finset.coe_union, Set.biInter_union]
    rfl
  filter_upwards [ae_all_iff.2 (fun t => h (cell t) (hcell t))] with ω hω
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro _ ⟨t, rfl⟩
    exact hcell t
  · intro u hu x hx
    obtain ⟨s, hs, hxs, hsu⟩ := hB.exists_subset_of_mem_open hx hu
    have hsingle : cell {⟨s, hs⟩} = s := Finset.set_biInter_singleton _ _
    exact ⟨s, ⟨_, hsingle⟩, hB.mem_nhds hs hxs, hsu⟩
  · rintro _ ⟨t, rfl⟩
    exact hω t

/-- **Almost sure convergence of the empirical law in the Mallows metric** (P. J. Bickel and
D. A. Freedman, *Ann. Statist.* 9 (1981), Lemma 8.4, and (2.1) for `p = 2` on the line). Let
`E` be a separable Banach space, `1 ≤ p < ∞`, and `X₀, X₁, …` i.i.d. `E`-valued with law
`μ ∈ Γ_p` (finite `p`-th moment). If `F n ω` is the empirical law `(n+1)⁻¹ ∑_{i ≤ n} δ_{X_i(ω)}`,
then `d_p(F n ω, μ) → 0` for almost every `ω`. -/
theorem tendsto_wasserstein_empirical {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {p : ℝ} (hp : 1 ≤ p) {X : ℕ → Ω → E}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (μ : ProbabilityMeasure E)
    (hlaw : P.map (X 0) = (μ : Measure E)) (hmom : ∫⁻ x, ‖x‖ₑ ^ p ∂(μ : Measure E) < ∞)
    (F : ℕ → Ω → ProbabilityMeasure E)
    (hF : ∀ n ω, (F n ω : Measure E) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range (n + 1), Measure.dirac (X i ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => wasserstein p (F n ω) μ) atTop (𝓝 0) := by
  have htest := empirical_integral_tendsto (hmeas 0) hindep hident μ hlaw F hF
  have hweak := empirical_weak_tendsto (P := P) F μ (by
    intro s hs
    have h := htest (s.indicator 1) (measurable_const.indicator hs)
      ((integrable_const (1 : ℝ)).indicator hs)
    simpa only [integral_indicator_one hs, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      NNReal.tendsto_coe] using h)
  let m (x : E) := ‖x‖ₑ ^ p
  have hm : Measurable m := measurable_eNorm.pow_const _
  have hmfin x : m x ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans hp) eNorm_ne_top
  have hreal (ρ : ProbabilityMeasure E) :
      ∫ x, (m x).toReal ∂(ρ : Measure E) = (∫⁻ x, m x ∂(ρ : Measure E)).toReal :=
    integral_toReal hm.aemeasurable (ae_of_all _ fun x => (hmfin x).lt_top)
  have hmoment := htest (fun x => (m x).toReal) hm.ennreal_toReal
    (integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmom.ne)
  simp only [hreal] at hmoment
  filter_upwards [hweak, hmoment] with ω hω hωm
  have hfinite n : (∫⁻ x, m x ∂(F n ω : Measure E)) ≠ ∞ := by
    rw [hF, lintegral_smul_measure, lintegral_finsetSum_measure]
    simp only [lintegral_dirac, smul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr fun i _ => hmfin (X i ω))
  have hmoment := (ENNReal.tendsto_toReal_iff hfinite hmom.ne).mp hωm
  exact (tendsto_wasserstein_iff hp (0 : E) (fun n => F n ω) μ
    (by simpa only [edist_zero_left, m, eNorm_eq_nnNorm] using fun n => (hfinite n).lt_top)
    (by simpa only [edist_zero_left, eNorm_eq_nnNorm] using hmom)).2
      ⟨hω, by simpa only [edist_zero_left, m, eNorm_eq_nnNorm] using hmoment⟩

end MathlibExt.Probability.Statistics.BootstrapWanted
