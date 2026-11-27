/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Convergence in Wasserstein distance implies weak convergence

The elementary half of the Kantorovich–Rubinstein formula for real Lipschitz test functions,
`|∫ f dμ - ∫ f dν| ≤ L · W_1(μ, ν)`, and its consequence: if `W_p(μ_k, μ) → 0` for some
`p ≥ 1`, then `μ_k → μ` weakly. This is one half of the first part of Theorem 6.9 of
C. Villani, *Optimal Transport: Old and New*, Springer 2009 (convergence in `W_p` implies weak
convergence); the full statement, including convergence of `p`-th moments and the converse, is the
`WantedExt` entry `MathlibExt.MeasureTheory.WassersteinWanted.tendsto_wasserstein_iff`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)

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
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul _ measurable_edist]
  refine lintegral_mono fun z => ?_
  rw [← edist_eq_enorm_sub]
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
    rw [edist_eq_enorm_sub]
    refine (enorm_integral_sub_le_mul_wasserstein_one hL (hint _) (hint _)).trans ?_
    gcongr
    exact wasserstein_mono one_pos hp _ _
  have hlim : Tendsto (fun k => (L : ℝ≥0∞) * wasserstein p (μs k) μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
