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
import MathlibExt.Probability.SkorokhodRepresentation

/-!
# Almost sure convergence of the empirical law in the Mallows metric

For `1 ≤ p`, the empirical laws of an i.i.d. sequence with finite `p`-th moment converge
almost surely to the common law in Wasserstein distance (`tendsto_wasserstein_empirical`).
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
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

/-- A varying integrable bound suffices in dominated convergence if its integral also converges.
We clip the unused part of the bound at its pointwise limit. -/
private theorem lintegral_tendsto_zero {α : Type*} [MeasurableSpace α] {Q : Measure α}
    {d b : ℕ → α → ℝ≥0∞} {a : α → ℝ≥0∞}
    (hd : ∀ n, Measurable (d n)) (hb : ∀ n, Measurable (b n)) (ha : Measurable a)
    (hle : ∀ n x, d n x ≤ b n x) (hfin : ∫⁻ x, a x ∂Q ≠ ∞)
    (hdlim : ∀ᵐ x ∂Q, Tendsto (fun n => d n x) atTop (𝓝 0))
    (hblim : ∀ᵐ x ∂Q, Tendsto (fun n => b n x) atTop (𝓝 (a x)))
    (hbint : Tendsto (fun n => ∫⁻ x, b n x ∂Q) atTop (𝓝 (∫⁻ x, a x ∂Q))) :
    Tendsto (fun n => ∫⁻ x, d n x ∂Q) atTop (𝓝 0) := by
  let g (n : ℕ) (x : α) := min (a x) (b n x - d n x)
  have hg n : Measurable (g n) := ha.min ((hb n).sub (hd n))
  have hga n x : g n x ≤ a x := min_le_left _ _
  have hgint : Tendsto (fun n => ∫⁻ x, g n x ∂Q) atTop (𝓝 (∫⁻ x, a x ∂Q)) := by
    apply tendsto_lintegral_of_dominated_convergence a hg (fun n => ae_of_all _ (hga n)) hfin
    filter_upwards [hdlim, hblim] with x hx hy
    simpa [g] using (tendsto_const_nhds (x := a x)).min
      (ENNReal.Tendsto.sub hy hx (.inr ENNReal.zero_ne_top))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n => (∫⁻ x, b n x ∂Q) - ∫⁻ x, g n x ∂Q) atTop (𝓝 0) by
      simpa using ENNReal.Tendsto.sub hbint hgint (.inl hfin))
    (Eventually.of_forall fun _ => bot_le)
  refine Eventually.of_forall fun n => ENNReal.le_sub_of_add_le_left
    (ne_top_of_le_ne_top hfin (lintegral_mono (hga n))) ?_
  rw [← lintegral_add_left (hg n)]
  exact lintegral_mono fun x => (add_le_add_left (min_le_right _ _) _).trans_eq
    (tsub_add_cancel_of_le (hle n x))

/-- Use a Skorokhod coupling for the weak limit. Its distance cost tends to zero pointwise,
and its moment bound has convergent integrals. -/
private theorem wasserstein_tendsto_of_moments {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) (ν : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hweak : Tendsto ν atTop (𝓝 μ)) (hfin : ∫⁻ x, ‖x‖ₑ ^ p ∂(μ : Measure E) < ∞)
    (hmom : Tendsto (fun n => ∫⁻ x, ‖x‖ₑ ^ p ∂(ν n : Measure E)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ p ∂(μ : Measure E)))) :
    Tendsto (fun n => wasserstein p (ν n) μ) atTop (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let Q := volume.restrict (Set.Icc (0 : ℝ) 1)
  obtain ⟨Y, Z, hY, hZ, hν, hμ, hlim⟩ :=
    SkorokhodRepresentationWanted.skorokhod_representation ν μ hweak
  let m (x : E) := ‖x‖ₑ ^ p
  have hm : Measurable m := measurable_eNorm.pow_const _
  let c : ℝ≥0∞ := 2 ^ (p - 1)
  have hc : c ≠ ∞ := by
    dsimp [c]
    finiteness
  let d (n : ℕ) (x : ℝ) := edist (Y n x) (Z x) ^ p
  let b (n : ℕ) (x : ℝ) := c * (m (Y n x) + m (Z x))
  let a (x : ℝ) := c * (m (Z x) + m (Z x))
  have ha : Measurable a := ((hm.comp hZ).add (hm.comp hZ)).const_mul _
  have hb n : Measurable (b n) := ((hm.comp (hY n)).add (hm.comp hZ)).const_mul _
  have hd n : Measurable (d n) := ((hY n).edist hZ).pow_const _
  have hd_le n x : d n x ≤ b n x := by
    refine (ENNReal.rpow_le_rpow ?_ hp0.le).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow ‖Y n x‖ₑ ‖Z x‖ₑ hp)
    simpa only [edist_comm 0 (Z x), edist_zero_right] using edist_triangle (Y n x) 0 (Z x)
  have intZ : ∫⁻ x, m (Z x) ∂Q = ∫⁻ x, m x ∂(μ : Measure E) := by
    rw [← hμ, lintegral_map hm hZ]
  have intY n : ∫⁻ x, m (Y n x) ∂Q = ∫⁻ x, m x ∂(ν n : Measure E) := by
    rw [← hν, lintegral_map hm (hY n)]
  have intA : ∫⁻ x, a x ∂Q = c * ((∫⁻ x, m x ∂(μ : Measure E)) +
      ∫⁻ x, m x ∂(μ : Measure E)) := by
    dsimp only [a]
    rw [lintegral_const_mul' _ _ hc,
      lintegral_add_left (f := fun x => m (Z x)) (hm.comp hZ), intZ]
  have intB n : ∫⁻ x, b n x ∂Q = c * ((∫⁻ x, m x ∂(ν n : Measure E)) +
      ∫⁻ x, m x ∂(μ : Measure E)) := by
    dsimp only [b]
    rw [lintegral_const_mul' _ _ hc,
      lintegral_add_left (f := fun x => m (Y n x)) (hm.comp (hY n)), intY, intZ]
  have hcost : Tendsto (fun n => ∫⁻ x, d n x ∂Q) atTop (𝓝 0) := by
    apply lintegral_tendsto_zero hd hb ha hd_le
    · rw [intA]
      exact ENNReal.mul_ne_top hc (ENNReal.add_ne_top.mpr ⟨hfin.ne, hfin.ne⟩)
    · filter_upwards [hlim] with x hx
      simpa only [Function.comp_def, d, edist_self, ENNReal.zero_rpow_of_pos hp0] using
        (ENNReal.continuous_rpow_const (y := p)).continuousAt.tendsto.comp
          (hx.edist (tendsto_const_nhds (x := Z x)))
    · filter_upwards [hlim] with x hx
      have hy : Tendsto (fun n => m (Y n x)) atTop (𝓝 (m (Z x))) :=
        (ENNReal.continuous_rpow_const.comp continuous_eNorm).continuousAt.tendsto.comp hx
      exact ENNReal.Tendsto.const_mul (hy.add tendsto_const_nhds) (.inr hc)
    · simp only [intB, intA]
      exact ENNReal.Tendsto.const_mul (hmom.add tendsto_const_nhds) (.inr hc)
  have hQ : IsProbabilityMeasure Q := ⟨by simp [Q]⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n => (∫⁻ x, d n x ∂Q) ^ (1 / p)) atTop (𝓝 0) by
      simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] using
        (ENNReal.continuous_rpow_const (y := 1 / p)).continuousAt.tendsto.comp hcost)
    (Eventually.of_forall fun _ => bot_le)
  refine Eventually.of_forall fun n => ?_
  let pair (x : ℝ) := (Y n x, Z x)
  have hpair : Measurable pair := (hY n).prodMk hZ
  let π : ProbabilityMeasure (E × E) := ⟨Q.map pair, inferInstance⟩
  have hπ : IsCoupling (ν n) μ π := by
    constructor
    · change _ = (Q.map pair).map Prod.fst
      rw [Measure.map_map measurable_fst hpair]
      exact (hν n).symm
    · change _ = (Q.map pair).map Prod.snd
      rw [Measure.map_map measurable_snd hpair]
      exact hμ.symm
  have H := wasserstein_le_of_isCoupling hp0.le hπ
  change _ ≤ (∫⁻ z : E × E, edist z.1 z.2 ^ p ∂Q.map pair) ^ (1 / p) at H
  rw [lintegral_map ((measurable_fst.edist measurable_snd).pow_const _) hpair] at H
  exact H

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
  apply wasserstein_tendsto_of_moments hp _ μ hω hmom
  refine (ENNReal.tendsto_toReal_iff (fun n => ?_) hmom.ne).mp hωm
  rw [hF, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr fun i _ => hmfin (X i ω))

end MathlibExt.Probability.Statistics.BootstrapWanted
