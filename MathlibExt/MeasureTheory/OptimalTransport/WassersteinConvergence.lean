/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.DiracProba
import MathlibExt.Probability.SkorokhodRepresentation

/-!
# Wasserstein distances and weak convergence

The elementary half of the Kantorovich–Rubinstein formula states that for an `L`-Lipschitz
real function integrable under both probability measures, the difference of its integrals
is at most `L · W_1`. On second-countable (pseudo-)extended metric spaces with measurable open
sets, this implies that `W_p(μ_k, μ) → 0` for `p ≥ 1` entails weak convergence.

On a Polish metric space with its Borel σ-algebra, if `p ≥ 1` and the probability measures `μ_k`
and `μ` have finite `p`-th moments about `x₀`, convergence in `W_p` is equivalent to weak
convergence together with convergence of those moments. The forward direction measures distances
from the Dirac mass at `x₀`; the reverse direction uses a Skorokhod coupling and dominated
convergence with a varying bound.

## References

* Cédric Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen
  Wissenschaften 338, Springer, 2009, Chapter 6, pp. 93–111, Remark 6.5, Definition 6.8(i),
  and Theorem 6.9. The Dirac-moment identity is used in the proof of Lemma 6.14.
* A. V. Skorokhod, *Limit Theorems for Stochastic Processes*, Theory of Probability & Its
  Applications 1(3) (1956), pp. 261–290, for the representation theorem. We use
  `skorokhod_representation` from `MathlibExt.Probability.SkorokhodRepresentation`.
* The Dirac-marginal argument adapts `wasserstein_dirac` from
  `MathlibExt.MeasureTheory.OptimalTransport.Wasserstein`. The converse adapts
  `wasserstein_tendsto_of_moments` and `lintegral_tendsto_zero` from
  `MathlibExt.Probability.Statistics.EmpiricalMallows`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling isCoupling_iff_map)

namespace MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X]

/-- **Kantorovich–Rubinstein bound for real Lipschitz functions.** If `f : X → ℝ` is
`L`-Lipschitz and integrable for `μ` and `ν`, then `|∫ f dμ - ∫ f dν| ≤ L · W_1(μ, ν)`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Remark 6.5, the inequality `≥` in
formula (6.3) for `L = 1`). -/
theorem enorm_integral_sub_le_mul_wasserstein_one {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {μ ν : ProbabilityMeasure X} (hfμ : Integrable f (μ : Measure X))
    (hfν : Integrable f (ν : Measure X)) :
    ‖∫ x, f x ∂(μ : Measure X) - ∫ x, f x ∂(ν : Measure X)‖ₑ ≤ L * wasserstein 1 μ ν := by
  have hfm : Measurable f := hf.continuous.measurable
  have : Nonempty {π : ProbabilityMeasure (X × X) // IsCoupling μ ν π} :=
    ⟨⟨μ.prod ν, isCoupling_prod μ ν⟩⟩
  simp only [wasserstein, transportCost, div_one, ENNReal.rpow_one]
  rw [iInf_subtype', ENNReal.mul_iInf (by simp)]
  refine le_iInf fun ⟨π, h1, h2⟩ => ?_
  have hf1 : Integrable (fun z : X × X => f z.1) (π : Measure (X × X)) := by
    rw [h1] at hfμ
    exact (integrable_map_measure hfm.aestronglyMeasurable measurable_fst.aemeasurable).1 hfμ
  have hf2 : Integrable (fun z : X × X => f z.2) (π : Measure (X × X)) := by
    rw [h2] at hfν
    exact (integrable_map_measure hfm.aestronglyMeasurable measurable_snd.aemeasurable).1 hfν
  have e : ∫ x, f x ∂(μ : Measure X) - ∫ x, f x ∂(ν : Measure X) =
      ∫ z, (f z.1 - f z.2) ∂(π : Measure (X × X)) := by
    rw [integral_sub hf1 hf2, h1, h2, integral_map measurable_fst.aemeasurable
      hfm.aestronglyMeasurable, integral_map measurable_snd.aemeasurable hfm.aestronglyMeasurable]
  rw [e]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  rw [← lintegral_const_mul _ measurable_edist]
  refine lintegral_mono fun z => ?_
  rw [← eDist_eq_eNorm_sub]
  exact hf.edist_le_mul z.1 z.2

/-- **Convergence in Wasserstein distance implies weak convergence.** If `p ≥ 1` and
`W_p(μ_k, μ) → 0`, then `μ_k → μ` in the topology of weak convergence
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 6.9, the implication from
`W_p(μ_k, μ) → 0` to the weak convergence part of Definition 6.8). The proof bounds the integrals of
bounded Lipschitz functions by `W_1 ≤ W_p`. -/
theorem tendsto_of_tendsto_wasserstein {p : ℝ} (hp : 1 ≤ p) {μs : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (h : Tendsto (fun k => wasserstein p (μs k) μ) atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 μ) := by
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  let f' : BoundedContinuousFunction X ℝ :=
    { toFun := f, continuous_toFun := hL.continuous, map_bounded' := ⟨C, hC⟩ }
  have hint : ∀ ρ : ProbabilityMeasure X, Integrable f (ρ : Measure X) :=
    fun ρ => f'.integrable (ρ : Measure X)
  rw [tendsto_iff_edist_tendsto_0]
  have hbound : ∀ k, edist (∫ x, f x ∂(μs k : Measure X)) (∫ x, f x ∂(μ : Measure X)) ≤
      L * wasserstein p (μs k) μ := by
    intro k
    rw [eDist_eq_eNorm_sub]
    refine (enorm_integral_sub_le_mul_wasserstein_one hL (hint _) (hint _)).trans ?_
    gcongr
    exact wasserstein_mono one_pos hp _ _
  have hlim : Tendsto (fun k => (L : ℝ≥0∞) * wasserstein p (μs k) μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.MeasureTheory.WassersteinWanted

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
open MathlibExt.Probability.SkorokhodRepresentationWanted (skorokhod_representation)

section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- For positive `p`, the distance from a Dirac mass is the `p`-th root of the moment. -/
private theorem wasserstein_diracProba_left {p : ℝ} (hp : 0 < p) (x₀ : X)
    (ν : ProbabilityMeasure X) :
    wasserstein p (diracProba x₀) ν = (∫⁻ x, edist x₀ x ^ p ∂(ν : Measure X)) ^ (1 / p) := by
  let δ := diracProba x₀
  have hm : Measurable (fun x : X => edist x₀ x ^ p) :=
    (measurable_const.edist measurable_id).pow_const p
  have hcost (π : ProbabilityMeasure (X × X)) (hπ : IsCoupling δ ν π) :
      ∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X)) =
        ∫⁻ x, edist x₀ x ^ p ∂(ν : Measure X) := by
    obtain ⟨hfst, hsnd⟩ := (isCoupling_iff_map δ ν π).1 hπ
    have hδ : ∀ᵐ x ∂(π : Measure (X × X)).map Prod.fst, x = x₀ := by
      rw [← ProbabilityMeasure.toMeasure_map π, hfst]
      change ∀ᵐ x ∂Measure.dirac x₀, x = x₀
      simp [ae_dirac_eq]
    have hae : ∀ᵐ z ∂(π : Measure (X × X)), z.1 = x₀ :=
      ae_of_ae_map measurable_fst.aemeasurable hδ
    calc
      _ = ∫⁻ z, edist x₀ z.2 ^ p ∂(π : Measure (X × X)) :=
        lintegral_congr_ae (hae.mono fun z hz => by rw [hz])
      _ = _ := by
        rw [← lintegral_map hm measurable_snd, ← ProbabilityMeasure.toMeasure_map π, hsnd]
  refine le_antisymm ((wasserstein_le_of_isCoupling hp.le (isCoupling_prod δ ν)).trans_eq ?_) ?_
  · rw [hcost _ (isCoupling_prod δ ν)]
  · rw [wasserstein_eq_iInf hp]
    exact le_iInf₂ fun π hπ => (congrArg (· ^ (1 / p)) (hcost π hπ)).ge

/-- Wasserstein convergence forces convergence of the moments about any fixed point. -/
private theorem tendsto_moments_of_tendsto_wasserstein [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p)
    (x₀ : X) {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : Tendsto (fun k => wasserstein p (μs k) μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x, edist x₀ x ^ p ∂(μs k : Measure X)) atTop
      (𝓝 (∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X))) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let δ := diracProba x₀
  have hroot : Tendsto (fun k => wasserstein p δ (μs k)) atTop (𝓝 (wasserstein p δ μ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [tsub_zero] using (ENNReal.Tendsto.sub
        (tendsto_const_nhds (x := wasserstein p δ μ)) h (Or.inr ENNReal.zero_ne_top)))
      (by simpa only [add_zero] using (tendsto_const_nhds (x := wasserstein p δ μ)).add h)
      (fun k => tsub_le_iff_right.mpr (wasserstein_triangle hp δ (μs k) μ)) (fun k => ?_)
    rw [wasserstein_comm p (μs k) μ]
    exact wasserstein_triangle hp δ μ (μs k)
  have hpow (ν : ProbabilityMeasure X) :
      wasserstein p δ ν ^ p = ∫⁻ x, edist x₀ x ^ p ∂(ν : Measure X) := by
    rw [wasserstein_diracProba_left hp0, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  simpa only [Function.comp_def, hpow] using
    (ENNReal.continuous_rpow_const (y := p)).continuousAt.tendsto.comp hroot

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

/-- For a Skorokhod coupling, the distance cost tends to zero almost everywhere,
and its moment bound has convergent integrals. -/
private theorem wasserstein_tendsto_of_moments [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) (x₀ : X)
    (ν : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hweak : Tendsto ν atTop (𝓝 μ)) (hfin : ∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X) < ∞)
    (hmom : Tendsto (fun n => ∫⁻ x, edist x₀ x ^ p ∂(ν n : Measure X)) atTop
      (𝓝 (∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X)))) :
    Tendsto (fun n => wasserstein p (ν n) μ) atTop (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let Q := volume.restrict (Set.Icc (0 : ℝ) 1)
  obtain ⟨Y, Z, hY, hZ, hν, hμ, hlim⟩ :=
    skorokhod_representation ν μ hweak
  let m (x : X) := edist x₀ x ^ p
  have hm : Measurable m := (measurable_const.edist measurable_id).pow_const _
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
      (ENNReal.rpow_add_le_mul_rpow_add_rpow (edist x₀ (Y n x)) (edist x₀ (Z x)) hp)
    simpa only [edist_comm (Y n x) x₀] using edist_triangle (Y n x) x₀ (Z x)
  have intZ : ∫⁻ x, m (Z x) ∂Q = ∫⁻ x, m x ∂(μ : Measure X) := by
    rw [← hμ, lintegral_map hm hZ]
  have intY n : ∫⁻ x, m (Y n x) ∂Q = ∫⁻ x, m x ∂(ν n : Measure X) := by
    rw [← hν n, lintegral_map hm (hY n)]
  have intA : ∫⁻ x, a x ∂Q = c * ((∫⁻ x, m x ∂(μ : Measure X)) +
      ∫⁻ x, m x ∂(μ : Measure X)) := by
    dsimp only [a]
    rw [lintegral_const_mul' _ _ hc,
      lintegral_add_left (f := fun x => m (Z x)) (hm.comp hZ), intZ]
  have intB n : ∫⁻ x, b n x ∂Q = c * ((∫⁻ x, m x ∂(ν n : Measure X)) +
      ∫⁻ x, m x ∂(μ : Measure X)) := by
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
      have hm_cont : Continuous m :=
        ENNReal.continuous_rpow_const.comp (continuous_const.edist continuous_id)
      have hy : Tendsto (fun n => m (Y n x)) atTop (𝓝 (m (Z x))) :=
        hm_cont.continuousAt.tendsto.comp hx
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
  let π : ProbabilityMeasure (X × X) := ⟨Q.map pair, inferInstance⟩
  have hπ : IsCoupling (ν n) μ π := by
    apply (isCoupling_iff_map (ν n) μ π).2
    constructor
    · apply Subtype.ext
      change (Q.map pair).map Prod.fst = (ν n : Measure X)
      rw [Measure.map_map measurable_fst hpair]
      exact hν n
    · apply Subtype.ext
      change (Q.map pair).map Prod.snd = (μ : Measure X)
      rw [Measure.map_map measurable_snd hpair]
      exact hμ
  refine (wasserstein_le_of_isCoupling hp0.le hπ).trans_eq ?_
  congr 1
  exact lintegral_map ((measurable_fst.edist measurable_snd).pow_const p) hpair

end

/-- **The Wasserstein distance metrizes weak convergence in `P_p`.** Let `X` be a Polish metric
space, `p ∈ [1, ∞)`, `x₀ ∈ X`, and let `μ_k` and `μ` be probability measures with finite
`p`-th moments `∫ d(x₀, x)^p`. Then `W_p(μ_k, μ) → 0` if and only if `μ_k → μ` weakly and
`∫ d(x₀, x)^p dμ_k → ∫ d(x₀, x)^p dμ` (C. Villani, *Optimal Transport: Old and New*, Springer
2009, Theorem 6.9 with characterization (i) of Definition 6.8). The topology on
`ProbabilityMeasure X` is the topology of weak convergence. -/
theorem tendsto_wasserstein_iff {X : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] {p : ℝ} (hp : 1 ≤ p) (x₀ : X)
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμs : ∀ k, ∫⁻ x, edist x₀ x ^ p ∂(μs k : Measure X) < ∞)
    (hμ : ∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X) < ∞) :
    Tendsto (fun k => wasserstein p (μs k) μ) atTop (𝓝 0) ↔
      Tendsto μs atTop (𝓝 μ) ∧
        Tendsto (fun k => ∫⁻ x, edist x₀ x ^ p ∂(μs k : Measure X)) atTop
          (𝓝 (∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X))) := by
  -- Keep the finite-moment hypothesis of the original `P_p` statement.
  have _ := hμs
  constructor
  · intro h
    exact ⟨tendsto_of_tendsto_wasserstein hp h, tendsto_moments_of_tendsto_wasserstein hp x₀ h⟩
  · rintro ⟨hweak, hmoment⟩
    exact wasserstein_tendsto_of_moments hp x₀ μs μ hweak hμ hmoment

end MathlibExt.MeasureTheory.WassersteinWanted
