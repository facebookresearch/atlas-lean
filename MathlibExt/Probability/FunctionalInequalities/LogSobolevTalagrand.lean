/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Logarithmic Sobolev and Talagrand inequalities on metric measure spaces

On a metric space `X` with a Borel probability measure `m`:

* the **logarithmic Sobolev inequality** with constant `α > 0` asks that
  `2α ∫ f log f dm ≤ ∫_{f > 0} |∇f|² / f dm` for every nonnegative Lipschitz `f` with
  `∫ f dm = 1`, where `|∇f|` is the local Lipschitz constant;
* the **Talagrand (quadratic transport-cost) inequality** with constant `C` asks that
  `W₂(μ, m)² ≤ C Ent_m(μ)` for every probability measure `μ`, where `Ent_m(μ)` is the relative
  entropy (Kullback–Leibler divergence) of `μ` with respect to `m`.

These are the formulations of N. Gigli and M. Ledoux, *From log Sobolev to Talagrand: a quick
proof*, Discrete Contin. Dyn. Syst. Ser. A (2013): formulation (i) of their
Proposition 5.1 and inequality (2.3). The entropy `∫ f log f dm` of a density `f` is written as
the Kullback–Leibler divergence `KL(f m ‖ m)`, which is Gigli and Ledoux's `Ent_m(f m)` (their
Section 2); Mathlib's `InformationTheory.klDiv` takes values in `[0, ∞]`.

Both predicates are stated for a probability measure `m`, as in the source: `SatisfiesLogSobolev`
takes an instance `IsProbabilityMeasure m` and `SatisfiesTalagrand` a `ProbabilityMeasure`. For
the zero measure the log-Sobolev inequality would hold vacuously, since no density has
`∫ f dm = 1`; and `KL(f m ‖ m) = ∫ f log f dm` uses that `f m` and `m` have the same mass, since
Mathlib's Kullback–Leibler divergence of general finite measures carries a mass correction.

The theorem of F. Otto and C. Villani (log-Sobolev with constant `α` implies Talagrand with
constant `2/α`) is proved in `MathlibExt.Probability.FunctionalInequalities.OttoVillani`.
This module defines the two predicates and shows that Dirac masses satisfy them.

## Main definitions

* `localLipschitzConstant`: `|∇f|(x) = limsup_{y → x} |f(y) - f(x)| / d(x, y)`.
* `SatisfiesLogSobolev`, `SatisfiesTalagrand`.

## Main results

* `satisfiesLogSobolev_dirac`, `satisfiesTalagrand_dirac`.
* `SatisfiesTalagrand.wasserstein_one_sq_le`: the inequality also bounds `W₁`.
-/

@[expose] public section

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
  (wasserstein wasserstein_self wasserstein_mono)

namespace MathlibExt.Probability.LogSobolevTalagrand

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- **Local Lipschitz constant (slope).** For `f : X → ℝ` on a metric space,
`|∇f|(x) = limsup_{y → x} |f(y) - f(x)| / d(x, y)`, with values in `[0, ∞]`, taken over `y ≠ x`,
and equal to `0` at isolated points (N. Gigli and M. Ledoux, *From log Sobolev to Talagrand: a
quick proof*, Discrete Contin. Dyn. Syst. Ser. A (2013), Section 2; on a Riemannian manifold it is
the norm of the gradient of a `C¹` function). -/
noncomputable def localLipschitzConstant (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  limsup (fun y => ENNReal.ofReal (|f y - f x| / dist y x)) (𝓝[≠] x)

/-- **Logarithmic Sobolev inequality.** A probability measure `m` on a metric space satisfies the
logarithmic Sobolev inequality with constant `α` if for every nonnegative Lipschitz function `f`
with `∫ f dm = 1`,
`2α ∫ f log f dm ≤ ∫_{f > 0} |∇f|² / f dm`,
where `|∇f|` is the local Lipschitz constant and `∫ f log f dm` is the relative entropy
`KL(f m ‖ m)` of the probability measure `f m` (N. Gigli and M. Ledoux, *From log Sobolev to
Talagrand: a quick proof*, Discrete Contin. Dyn. Syst. Ser. A (2013), Proposition 5.1,
formulation (i); for the standard Gaussian measure on `ℝⁿ` this holds with `α = 1`, Gross'
inequality). For the zero measure, which is excluded, it would hold vacuously. -/
def SatisfiesLogSobolev (m : Measure X) [IsProbabilityMeasure m] (α : ℝ) : Prop :=
  ∀ f : X → ℝ, (∃ K, LipschitzWith K f) → (∀ x, 0 ≤ f x) → ∫ x, f x ∂m = 1 →
    ENNReal.ofReal (2 * α) * klDiv (m.withDensity fun x => ENNReal.ofReal (f x)) m ≤
      ∫⁻ x in {x | 0 < f x}, localLipschitzConstant f x ^ 2 / ENNReal.ofReal (f x) ∂m

/-- **Talagrand's quadratic transport-cost inequality.** A probability measure `m` on a metric
space satisfies the Talagrand inequality with constant `C` if `W₂(μ, m)² ≤ C · KL(μ ‖ m)` for
every probability measure `μ` (N. Gigli and M. Ledoux, *From log Sobolev to Talagrand: a quick
proof*, Discrete Contin. Dyn. Syst. Ser. A (2013), inequality (2.3); M. Talagrand proved it for the
standard Gaussian measure on `ℝⁿ` with `C = 2`, Geom. Funct. Anal. 6 (1996)). In Villani's
notation, `T₂(λ)` is the case `C = 2/λ`. -/
def SatisfiesTalagrand (m : ProbabilityMeasure X) (C : ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure X,
    wasserstein 2 μ m ^ (2 : ℝ) ≤ ENNReal.ofReal C * klDiv (μ : Measure X) (m : Measure X)

/-- **Dirac masses satisfy the logarithmic Sobolev inequality.** For every `α`, the Dirac mass
`δ_{x₀}` satisfies `SatisfiesLogSobolev` with constant `α`: a density with `∫ f dδ_{x₀} = 1`
has `f(x₀) = 1`, so `f δ_{x₀} = δ_{x₀}` and the entropy vanishes. -/
theorem satisfiesLogSobolev_dirac [MeasurableSingletonClass X] (x₀ : X) (α : ℝ) :
    SatisfiesLogSobolev (Measure.dirac x₀) α := by
  intro f _ _ hint
  have hf1 : f x₀ = 1 := by rwa [integral_dirac] at hint
  have hwd : (Measure.dirac x₀).withDensity (fun x => ENNReal.ofReal (f x)) =
      Measure.dirac x₀ := by
    ext s hs
    classical
    rw [withDensity_apply _ hs, restrict_dirac' hs]
    by_cases hx : x₀ ∈ s
    · simp [hx, hf1]
    · simp [hx]
  rw [hwd, klDiv_self, mul_zero]
  exact bot_le

omit [MetricSpace X] in
/-- **Probability measures dominated by a Dirac mass.** A probability measure absolutely
continuous with respect to `δ_{x₀}` is `δ_{x₀}`. -/
theorem eq_dirac_of_absolutelyContinuous [MeasurableSingletonClass X] {x₀ : X}
    (μ : ProbabilityMeasure X) (hac : (μ : Measure X) ≪ Measure.dirac x₀) :
    (μ : Measure X) = Measure.dirac x₀ := by
  have h0 : (μ : Measure X) {x₀}ᶜ = 0 := hac (by simp)
  ext s hs
  by_cases hx : x₀ ∈ s
  · rw [Measure.dirac_apply_of_mem hx]
    have : (μ : Measure X) sᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) h0
    rwa [prob_compl_eq_zero_iff hs] at this
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem hx]
    refine measure_mono_null (t := {x₀}ᶜ) (fun y hy (hyx : y ∈ ({x₀} : Set X)) => hx ?_) h0
    rw [Set.mem_singleton_iff] at hyx
    exact hyx ▸ hy

/-- **Dirac masses satisfy the Talagrand inequality.** For every `C > 0`, `δ_{x₀}` satisfies
`SatisfiesTalagrand` with constant `C`: `KL(μ ‖ δ_{x₀}) = ∞` unless `μ = δ_{x₀}`, and
`W₂(δ_{x₀}, δ_{x₀}) = 0`. -/
theorem satisfiesTalagrand_dirac [MeasurableSingletonClass X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] (x₀ : X) {C : ℝ} (hC : 0 < C) :
    SatisfiesTalagrand (⟨Measure.dirac x₀, inferInstance⟩ : ProbabilityMeasure X) C := by
  intro μ
  by_cases hac : (μ : Measure X) ≪ Measure.dirac x₀
  · have hμ : μ = (⟨Measure.dirac x₀, inferInstance⟩ : ProbabilityMeasure X) :=
      Subtype.ext (eq_dirac_of_absolutelyContinuous μ hac)
    have h0 : wasserstein 2 μ (⟨Measure.dirac x₀, inferInstance⟩ : ProbabilityMeasure X) = 0 := by
      rw [← hμ]; exact wasserstein_self (by norm_num : (0 : ℝ) < 2) μ
    rw [h0]
    simp
  · change _ ≤ ENNReal.ofReal C * klDiv (μ : Measure X) (Measure.dirac x₀)
    rw [klDiv_of_not_ac hac, ENNReal.mul_top (by simpa using hC)]
    exact le_top

/-- **Talagrand's inequality bounds `W₁`.** If `m` satisfies Talagrand's quadratic inequality with
constant `C`, then `W₁(μ, m)² ≤ C · KL(μ ‖ m)` for every probability measure `μ`, because
`W₁ ≤ W₂` (C. Villani, *Optimal Transport: Old and New*, Springer 2009, Remark 6.6). This is the
`T₁` form of the transport inequality. -/
theorem SatisfiesTalagrand.wasserstein_one_sq_le [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : ProbabilityMeasure X} {C : ℝ} (h : SatisfiesTalagrand m C)
    (μ : ProbabilityMeasure X) :
    wasserstein 1 μ m ^ (2 : ℝ) ≤ ENNReal.ofReal C * klDiv (μ : Measure X) (m : Measure X) :=
  (ENNReal.rpow_le_rpow (wasserstein_mono one_pos one_le_two μ m) (by norm_num)).trans (h μ)

end MathlibExt.Probability.LogSobolevTalagrand
