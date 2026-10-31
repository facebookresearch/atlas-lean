/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# `L²` limits of Gaussian random vectors are Gaussian

Gaussian laws are closed under convergence in `L²(P)`: if real Gaussian random variables
`X n ~ N(m n, v n)` converge to `Y` in `L²`, then the means and variances converge and
`Y ~ N(E Y, Var Y)`. Pinned Mathlib has Gaussian measures, Gaussian laws and Gaussian processes
but no such closure statement. Since Mathlib's `IsGaussian` is defined through continuous linear
functionals, the real case gives the case of random vectors in a separable Banach space, and that
gives the closure of real Gaussian processes under coordinatewise `L²` limits.

## Main results

* `ProbabilityTheory.HasGaussianLaw.of_tendsto_eLpNorm_real`: real Gaussian random variables.
* `ProbabilityTheory.HasGaussianLaw.of_tendsto_eLpNorm`: Gaussian random vectors in a separable
  Banach space.
* `ProbabilityTheory.IsGaussianProcess.of_tendsto_eLpNorm`: real Gaussian processes, with
  `L²` convergence at every index.
* `ProbabilityTheory.tendsto_integral_mul_of_tendsto_eLpNorm`: `E[X n Z n] → E[Y W]` when
  `X n → Y` and `Z n → W` in `L²` (used to pass means and covariances to the limit).

## Implementation notes

The limit is only assumed almost everywhere strongly measurable; it is square integrable because
the `X n` are (Gaussian laws have all moments) and `eLpNorm (X n - Y) 2 P` is eventually finite.
That `P` is a probability measure follows from `HasGaussianLaw` and is not a hypothesis.

## References

* S. Janson, *Gaussian Hilbert Spaces*, Cambridge University Press, 1997, Chapter 1 (limits of
  centered Gaussian variables are Gaussian; this file also treats non-centered variables).
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 5.6 (Gaussianity of the solutions of linear equations).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

private theorem integral_mul_toLp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Y W : Ω → ℝ} (hY : MemLp Y 2 P) (hW : MemLp W 2 P) :
    inner ℝ (hY.toLp Y) (hW.toLp W) = ∫ ω, Y ω * W ω ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hY.coeFn_toLp, hW.coeFn_toLp] with ω h₁ h₂
  simp [h₁, h₂, mul_comm]

private theorem tendsto_pairing
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Z : ℕ → Ω → ℝ} {Y W : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hZ : ∀ n, MemLp (Z n) 2 P) (hY : MemLp Y 2 P)
    (hW : MemLp W 2 P)
    (h1 : Tendsto (fun n ↦ eLpNorm (X n - Y) 2 P) atTop (𝓝 0))
    (h2 : Tendsto (fun n ↦ eLpNorm (Z n - W) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, X n ω * Z n ω ∂P) atTop (𝓝 (∫ ω, Y ω * W ω ∂P)) := by
  have hx := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' X hX Y hY).2 h1
  have hz := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Z hZ W hW).2 h2
  simpa only [integral_mul_toLp] using hx.inner (𝕜 := ℝ) hz

/-- **Closure of real Gaussian laws under `L²` limits.** If each `X n` is a real Gaussian random
variable and `X n → Y` in `L²(P)`, then `Y` is Gaussian. -/
theorem HasGaussianLaw.of_tendsto_eLpNorm_real
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, HasGaussianLaw (X n) P) (hY : AEStronglyMeasurable Y P)
    (h : Tendsto (fun n ↦ eLpNorm (X n - Y) 2 P) atTop (𝓝 0)) : HasGaussianLaw Y P := by
  have : IsProbabilityMeasure P := (hX 0).isProbabilityMeasure
  have hx : ∀ n, MemLp (X n) 2 P := fun n ↦ (hX n).memLp_two
  have hy : MemLp Y 2 P := Lp.memLp_of_cauchy_tendsto (by norm_num) hx Y h
  have hm : Tendsto (fun n ↦ ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, Y ω ∂P)) := by
    apply tendsto_integral_of_L1' Y (Eventually.of_forall fun n ↦ (hX n).integrable)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ ↦ zero_le) (fun _ ↦ eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  have hs := tendsto_pairing hx hx hy hy h h
  have hv : Tendsto (fun n ↦ Var[X n; P]) atTop (𝓝 (Var[Y; P])) := by
    simpa only [variance_eq_sub (hx _), variance_eq_sub hy, Pi.pow_apply, pow_two]
      using hs.sub (hm.pow 2)
  have hi := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) h
  have hc := hi.tendstoInDistribution (fun n ↦ (hX n).aemeasurable)
  have hlaw : P.map Y = gaussianReal (∫ ω, Y ω ∂P) (Var[Y; P].toNNReal) := by
    apply Measure.ext_of_charFun
    funext t
    have hc' := hc.tendsto_charFun t
    have hg : Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop
        (𝓝 (charFun (gaussianReal (∫ ω, Y ω ∂P) (Var[Y; P].toNNReal)) t)) := by
      simp_rw [(hX _).map_eq_gaussianReal, charFun_gaussianReal,
        Real.toNNReal_of_nonneg (variance_nonneg _ _)]
      have hmc := Complex.continuous_ofReal.continuousAt.tendsto.comp hm
      have hvc := Complex.continuous_ofReal.continuousAt.tendsto.comp hv
      apply Complex.continuous_exp.continuousAt.tendsto.comp
      exact ((tendsto_const_nhds.mul hmc).mul tendsto_const_nhds).sub
        ((hvc.mul tendsto_const_nhds).div_const _)
    exact tendsto_nhds_unique hc' hg
  exact ⟨hY.aemeasurable, hlaw ▸ inferInstance⟩

/-- **Closure of Gaussian laws under `L²` limits.** If each `X n` is a Gaussian random vector in
a separable Banach space `E` and `X n → Y` in `L²(P)`, then `Y` is Gaussian. -/
theorem HasGaussianLaw.of_tendsto_eLpNorm
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {X : ℕ → Ω → E} {Y : Ω → E}
    (hX : ∀ n, HasGaussianLaw (X n) P) (hY : AEStronglyMeasurable Y P)
    (h : Tendsto (fun n ↦ eLpNorm (X n - Y) 2 P) atTop (𝓝 0)) : HasGaussianLaw Y P := by
  refine ⟨hY.aemeasurable, isGaussian_of_isGaussian_map fun L ↦ ?_⟩
  have hy := L.continuous.comp_aestronglyMeasurable hY
  have hx := fun n ↦ (hX n).map L
  have hl : Tendsto (fun n ↦ eLpNorm (L ∘ X n - L ∘ Y) 2 P) atTop (𝓝 0) := by
    have hb : ∀ n, eLpNorm (L ∘ X n - L ∘ Y) 2 P ≤
        ENNReal.ofReal ‖L‖ * eLpNorm (X n - Y) 2 P := by
      intro n
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((hx n).aemeasurable.aestronglyMeasurable.sub hy)
      exact Eventually.of_forall fun ω ↦ by
        simpa only [Pi.sub_apply, Function.comp_apply, ← L.map_sub] using
          L.le_opNorm (X n ω - Y ω)
    have ht := ENNReal.Tendsto.const_mul h
      (a := ENNReal.ofReal ‖L‖) (Or.inr ENNReal.ofReal_ne_top)
    simp only [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ ↦ zero_le) hb
  have hg := HasGaussianLaw.of_tendsto_eLpNorm_real hx hy hl
  rw [L.measurable.aemeasurable.map_map_of_aemeasurable hY.aemeasurable]
  exact hg.isGaussian_map

/-- **Closure of Gaussian processes under `L²` limits.** If each `X n` is a real Gaussian
process and `X n t → Y t` in `L²(P)` for every `t`, then `Y` is a Gaussian process. -/
theorem IsGaussianProcess.of_tendsto_eLpNorm
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {T : Type*} {X : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}
    (hX : ∀ n, IsGaussianProcess (X n) P) (hY : ∀ t, AEStronglyMeasurable (Y t) P)
    (h : ∀ t, Tendsto (fun n ↦ eLpNorm (X n t - Y t) 2 P) atTop (𝓝 0)) :
    IsGaussianProcess Y P := by
  classical
  refine ⟨fun I ↦ ?_⟩
  have hy : AEStronglyMeasurable (fun ω ↦ I.restrict (Y · ω)) P :=
    (AEMeasurable.of_eval fun (i : I) ↦ (hY i).aemeasurable).aestronglyMeasurable
  apply HasGaussianLaw.of_tendsto_eLpNorm (fun n ↦ (hX n).hasGaussianLaw I) hy
  have hm : ∀ n, AEStronglyMeasurable
      ((fun ω ↦ I.restrict (X n · ω)) - (fun ω ↦ I.restrict (Y · ω))) P :=
    fun n ↦ ((hX n).hasGaussianLaw I).aemeasurable.aestronglyMeasurable.sub hy
  have hcoord : ∀ n (i : I), AEStronglyMeasurable (X n i - Y i) P :=
    fun n i ↦ ((hX n).hasGaussianLaw_eval i).aemeasurable.aestronglyMeasurable.sub (hY i)
  have hb : ∀ n, eLpNorm
      ((fun ω ↦ I.restrict (X n · ω)) - (fun ω ↦ I.restrict (Y · ω))) 2 P ≤
      ∑ i : I, eLpNorm (X n i - Y i) 2 P := by
    intro n
    calc
      _ ≤ eLpNorm (fun ω ↦ ∑ i : I, ‖X n i ω - Y i ω‖) 2 P := by
        apply eLpNorm_mono_ae (hm n)
        apply Eventually.of_forall
        intro ω
        have hn : 0 ≤ ∑ i : I, ‖X n i ω - Y i ω‖ :=
          Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
        rw [Real.norm_of_nonneg hn]
        apply (pi_norm_le_iff_of_nonneg hn).2
        intro i
        exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ i : I, eLpNorm (fun ω ↦ ‖X n i ω - Y i ω‖) 2 P := by
        simpa only [Finset.sum_fn] using
          (eLpNorm_sum_le (μ := P) (p := 2)
            (f := fun (i : I) ω ↦ ‖X n i ω - Y i ω‖) (s := Finset.univ) (by norm_num))
      _ = ∑ i : I, eLpNorm (X n i - Y i) 2 P := by
        apply Finset.sum_congr rfl
        intro i _
        exact eLpNorm_norm _ (hcoord n i)
  have ht : Tendsto (fun n ↦ ∑ i : I, eLpNorm (X n i - Y i) 2 P) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun (i : I) _ ↦ h i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ zero_le) hb

/-- **Continuity of the second moment pairing in `L²`.** If `X n → Y` and `Z n → W` in `L²(P)`
(all square integrable), then `E[X n Z n] → E[Y W]`. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Z : ℕ → Ω → ℝ} {Y W : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hZ : ∀ n, MemLp (Z n) 2 P) (hY : MemLp Y 2 P)
    (hW : MemLp W 2 P)
    (h1 : Tendsto (fun n ↦ eLpNorm (X n - Y) 2 P) atTop (𝓝 0))
    (h2 : Tendsto (fun n ↦ eLpNorm (Z n - W) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, X n ω * Z n ω ∂P) atTop (𝓝 (∫ ω, Y ω * W ω ∂P)) := by
  exact tendsto_pairing hX hZ hY hW h1 h2

end ProbabilityTheory
