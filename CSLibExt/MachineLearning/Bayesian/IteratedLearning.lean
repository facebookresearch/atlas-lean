/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MetropolisHastings
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Iterated learning: posterior sampling preserves the prior

Finite-hypothesis, finite-data form of the Griffiths–Kalish iterated-learning
model: each learner draws data from a hypothesis and the next learner samples a
hypothesis from the posterior. Hypotheses `H` and data `D` are finite; a datum
`d = (x, y)` folds the input distribution `q(x)` into the likelihood `L(d|h)`.

* `predictive π L`: the predictive law `P(d) = ∑ h, π h * L h d`, as `π.bind L`.
* `posterior π L d`: the posterior `P(h|d) = π h * L h d / P(d)` where `P(d) > 0`
  (and `π` where `P(d) = 0`, a case never reached from a hypothesis with
  positive likelihood). `posterior_mul_predictive` clears the denominator.
* `transmissionKernel π L`: the chain `K(h, h') = ∑ d, L h d * P(h'|d)` of
  equation (1), as `(L h).bind (posterior π L)`.
* `transmission_detailedBalance`: detailed balance
  `π h * K(h,h') = ∑ d, P(d) * P(h|d) * P(h'|d) = π h' * K(h',h)`.
* `transmission_stationary`: `π` is stationary, equation (2) with `p = π`,
  through `bind_eq_of_detailedBalance`; `invariant_transmissionKernel` is the
  kernel form through `IsReversible.invariant`, and
  `invariant_posterior_kernel_comp` is the abstract form through Mathlib's
  `posterior_comp_self`.
* `transmissionKernel_pos`, `transmissionKernel_eq_prior`,
  `transmissionKernel_eq_pure`: positivity under positive likelihoods, collapse
  to the prior under uninformative (hypothesis-independent) data, and collapse
  to the identity under disjoint likelihood supports.

Convergence to `π` is not claimed: it needs separate irreducibility and
aperiodicity hypotheses.

## References

* T. L. Griffiths and M. L. Kalish, "A Bayesian view of language evolution by
  iterated learning", *Proceedings of the 27th Annual Conference of the
  Cognitive Science Society* (2005); journal version *Cognitive Science* 31
  (2007) 441-480.
-/

@[expose] public section

namespace Cslib.MachineLearning.Bayesian.IteratedLearning

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **predictive distribution**: the law of a datum when the hypothesis is
drawn from the prior, `P(d) = ∑ h, π h * L h d`. -/
noncomputable def predictive (H : Type*) [Fintype H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) : PMF D :=
  π.bind L

/-- The predictive probability of `d` is the prior-weighted sum of likelihoods. -/
theorem predictive_apply (H : Type*) [Fintype H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) (d : D) :
    predictive H D π L d = ∑ h, π h * L h d := by
  rw [predictive, PMF.bind_apply, tsum_fintype]

/-- The **posterior**: `P(h|d) = π h * L h d / P(d)` where the predictive
probability is positive. Where it is zero the posterior is defined as the prior;
that case never arises from a hypothesis with positive likelihood. -/
noncomputable def posterior (H : Type*) [Fintype H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) (d : D) : PMF H :=
  if h : predictive H D π L d = 0 then π
  else PMF.ofFintype (fun h => π h * L h d / predictive H D π L d) (by
    simp_rw [ENNReal.div_eq_inv_mul, ← Finset.mul_sum,
      ← predictive_apply H D π L d]
    exact ENNReal.inv_mul_cancel h (PMF.apply_ne_top _ _))

/-- The posterior probability of `h` is prior times likelihood over evidence. -/
theorem posterior_apply (H : Type*) [Fintype H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) (d : D)
    (hd : predictive H D π L d ≠ 0) (h : H) :
    posterior H D π L d h = π h * L h d / predictive H D π L d := by
  rw [posterior, dite_eq_right hd, PMF.ofFintype_apply]

/-- A datum with positive likelihood under some hypothesis has positive
predictive probability, since the prior is everywhere positive. -/
theorem predictive_pos (H : Type*) [Fintype H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h) (h : H) (d : D)
    (hd : L h d ≠ 0) : predictive H D π L d ≠ 0 := by
  intro h0
  apply hd
  have hle := Finset.single_le_sum (s := Finset.univ)
    (fun i _ => zero_le (a := π i * L i d)) (Finset.mem_univ h)
  rw [predictive_apply] at h0
  rw [h0] at hle
  have hzero := le_zero_iff.mp hle
  rcases mul_eq_zero.mp hzero with hπ | hL
  · exact absurd hπ (ne_of_gt (hpos h))
  · exact hL

/-- Clearing the denominator: predictive times posterior is prior times
likelihood. With zero predictive probability both sides vanish, using the
positivity of the prior. -/
theorem posterior_mul_predictive (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h) (d : D)
    (h : H) :
    predictive H D π L d * posterior H D π L d h = π h * L h d := by
  by_cases hd : predictive H D π L d = 0
  · have hL0 : L h d = 0 := by
      rw [predictive_apply] at hd
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => zero_le (a := π i * L i d))).mp hd h (Finset.mem_univ h)
      rcases mul_eq_zero.mp hmem with hπ | hL
      · exact absurd hπ (ne_of_gt (hpos h))
      · exact hL
    rw [hd, hL0, zero_mul, mul_zero]
  · rw [posterior_apply H D π L d hd h]
    exact ENNReal.mul_div_cancel hd (PMF.apply_ne_top _ _)

/-- The predictive–posterior round trip: averaging the posterior over the
predictive law recovers the prior. This is the finite form of Mathlib's
`posterior_comp_self`. -/
theorem predictive_posterior_roundtrip (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h) (h : H) :
    ∑ d, predictive H D π L d * posterior H D π L d h = π h := by
  simp_rw [posterior_mul_predictive H D π L hpos]
  rw [← Finset.mul_sum]
  have hsum : ∑ d : D, L h d = 1 := by
    simpa [tsum_fintype] using (L h).tsum_coe
  rw [hsum, mul_one]

/-- The **transmission kernel** of equation (1): from `h`, draw a datum from
`L h` and then a hypothesis from the posterior. -/
noncomputable def transmissionKernel (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (h : H) : PMF H :=
  (L h).bind (posterior H D π L)

/-- Equation (1): `K(h, h') = ∑ d, L(d|h) * P(h'|d)`. -/
theorem transmissionKernel_apply (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (h h' : H) :
    transmissionKernel H D π L h h' = ∑ d, L h d * posterior H D π L d h' := by
  rw [transmissionKernel, PMF.bind_apply, tsum_fintype]

/-- One side of detailed balance, factored through the predictive law: both
`π h * K(h,h')` and `π h' * K(h',h)` equal this symmetric sum. -/
theorem transmission_detailedBalance_middle (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h)
    (h h' : H) :
    π h * transmissionKernel H D π L h h' = ∑ d, predictive H D π L d *
      (posterior H D π L d h * posterior H D π L d h') := by
  rw [transmissionKernel_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have key := posterior_mul_predictive H D π L hpos d h
  rw [← mul_assoc, ← key, mul_assoc]

/-- **Detailed balance**: `π h * K(h,h') = π h' * K(h',h)`. -/
theorem transmission_detailedBalance (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h)
    (h h' : H) :
    π h * transmissionKernel H D π L h h' =
      π h' * transmissionKernel H D π L h' h := by
  rw [transmission_detailedBalance_middle H D π L hpos h h',
    transmission_detailedBalance_middle H D π L hpos h' h]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm (posterior H D π L d h) (posterior H D π L d h')]

/-- **Stationarity** (equation (2) with `p = π`): one transmission step from the
prior stays at the prior. -/
theorem transmission_stationary (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h) :
    π.bind (transmissionKernel H D π L) = π :=
  Cslib.MachineLearning.Sampling.bind_eq_of_detailedBalance
    (transmission_detailedBalance H D π L hpos)

/-- The transmission kernel is reversible with respect to the prior. -/
theorem isReversible_transmissionKernel (H : Type*) [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h) :
    (Cslib.MachineLearning.Sampling.pmfKernel
      (transmissionKernel H D π L)).IsReversible π.toMeasure :=
  Cslib.MachineLearning.Sampling.isReversible_pmfKernel
    (transmission_detailedBalance H D π L hpos)

/-- Kernel form of stationarity, through Mathlib's `IsReversible.invariant`. -/
theorem invariant_transmissionKernel (H : Type*) [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] (D : Type*) [Fintype D]
    (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h) :
    (Cslib.MachineLearning.Sampling.pmfKernel
      (transmissionKernel H D π L)).Invariant π.toMeasure :=
  Kernel.IsReversible.invariant
    (isReversible_transmissionKernel H D π L hpos)

/-- Abstract stationarity through Mathlib's `posterior_comp_self`: drawing data
from the predictive law and then a hypothesis from the posterior returns the
prior, so posterior-then-likelihood composition leaves the prior invariant. -/
theorem invariant_posterior_kernel_comp (Ω : Type*) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (𝓧 : Type*) [MeasurableSpace 𝓧]
    (κ : Kernel Ω 𝓧) [IsMarkovKernel κ] (μ : Measure Ω) [IsFiniteMeasure μ] :
    (Kernel.comp (ProbabilityTheory.posterior κ μ) κ).Invariant μ := by
  rw [Kernel.Invariant, ← Measure.comp_assoc]
  exact posterior_comp_self

/-- With positive likelihoods everywhere, every transmission probability is
positive. -/
theorem transmissionKernel_pos (H : Type*) [Fintype H] (D : Type*) [Fintype D]
    [Nonempty D] (π : PMF H) (L : H → PMF D) (hposπ : ∀ h, 0 < π h)
    (hposL : ∀ h d, 0 < L h d) (h h' : H) :
    0 < transmissionKernel H D π L h h' := by
  rw [transmissionKernel_apply]
  obtain ⟨d₀, -⟩ := Finset.univ_nonempty (α := D)
  have hterm : L h d₀ * posterior H D π L d₀ h' ≠ 0 := by
    have hLd : L h d₀ ≠ 0 := ne_of_gt (hposL h d₀)
    have hPd := predictive_pos H D π L hposπ h d₀ hLd
    have hpost : posterior H D π L d₀ h' ≠ 0 := by
      rw [posterior_apply H D π L d₀ hPd h']
      exact ENNReal.div_ne_zero.mpr
        ⟨mul_ne_zero (ne_of_gt (hposπ h')) (ne_of_gt (hposL h' d₀)),
          PMF.apply_ne_top _ _⟩
    exact mul_ne_zero hLd hpost
  have hsum : ∑ d, L h d * posterior H D π L d h' ≠ ⊥ := by
    change ∑ d, L h d * posterior H D π L d h' ≠ 0
    rw [ne_eq, Finset.sum_eq_zero_iff_of_nonneg (fun (d : D)
      (_ : d ∈ Finset.univ) => zero_le (a := L h d * posterior H D π L d h'))]
    intro hall
    exact hterm (hall d₀ (Finset.mem_univ d₀))
  exact bot_lt_iff_ne_bot.mpr hsum

/-- **Uninformative data**: when the likelihood does not depend on the
hypothesis, the chain forgets in one step: `K(h, ·) = π`. -/
theorem transmissionKernel_eq_prior (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h)
    (q : PMF D) (hL : ∀ h, L h = q) (h : H) :
    transmissionKernel H D π L h = π := by
  have hP : ∀ d : D, predictive H D π L d = q d := by
    intro d
    rw [predictive_apply]
    simp_rw [hL]
    rw [← Finset.sum_mul]
    have hsum : ∑ h'' : H, π h'' = 1 := by
      simpa [tsum_fintype] using π.tsum_coe
    rw [hsum, one_mul]
  refine PMF.ext fun h' => ?_
  rw [transmissionKernel_apply]
  have hterm : ∀ d : D, L h d * posterior H D π L d h' = π h' * q d := by
    intro d
    have key := posterior_mul_predictive H D π L hpos d h'
    rw [hL h', hP d] at key
    have e1 : L h d = q d := by rw [hL h]
    rw [e1]
    exact key
  calc ∑ d, L h d * posterior H D π L d h'
      = ∑ d, π h' * q d := Finset.sum_congr rfl fun d _ => hterm d
    _ = π h' := by
      rw [← Finset.mul_sum]
      have hsum : ∑ d : D, q d = 1 := by
        simpa [tsum_fintype] using q.tsum_coe
      rw [hsum, mul_one]

/-- **Disjoint likelihood supports**: when no datum has positive likelihood
under two distinct hypotheses, the posterior concentrates on the hypothesis
that produced the datum, and the chain is the identity `K(h, ·) = pure h`. -/
theorem transmissionKernel_eq_pure (H : Type*) [Fintype H] (D : Type*)
    [Fintype D] (π : PMF H) (L : H → PMF D) (hpos : ∀ h, 0 < π h)
    (hdisj : ∀ h₁ h₂ : H, ∀ d : D, h₁ ≠ h₂ → L h₁ d ≠ 0 → L h₂ d = 0)
    (h : H) : transmissionKernel H D π L h = PMF.pure h := by
  classical
  have hP : ∀ d : D, L h d ≠ 0 → predictive H D π L d = π h * L h d := by
    intro d hd
    rw [predictive_apply]
    refine Finset.sum_eq_single h (fun b _ hb => ?_) (fun hb => ?_)
    · have hb0 : L b d = 0 := hdisj h b d (fun heq => hb heq.symm) hd
      rw [hb0, mul_zero]
    · exact absurd (Finset.mem_univ h) hb
  have hpost : ∀ d : D, ∀ h' : H, L h d ≠ 0 →
      posterior H D π L d h' = if h' = h then 1 else 0 := by
    intro d h' hd
    have hPd : predictive H D π L d ≠ 0 :=
      predictive_pos H D π L hpos h d hd
    rw [posterior_apply H D π L d hPd h', hP d hd]
    by_cases heq : h' = h
    · rw [heq, ite_eq_left rfl]
      exact ENNReal.div_self (mul_ne_zero (ne_of_gt (hpos h)) hd)
        (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
    · rw [ite_eq_right heq]
      have hb0 : L h' d = 0 := hdisj h h' d (fun heq' => heq heq'.symm) hd
      rw [hb0, mul_zero]
      exact ENNReal.zero_div
  refine PMF.ext fun h' => ?_
  rw [transmissionKernel_apply, PMF.pure_apply]
  by_cases heq : h' = h
  · rw [heq, ite_eq_left rfl]
    have hone : ∀ d : D, L h d * posterior H D π L d h = L h d := by
      intro d
      by_cases hd : L h d = 0
      · rw [hd, zero_mul]
      · rw [hpost d h hd, ite_eq_left rfl, mul_one]
    calc ∑ d, L h d * posterior H D π L d h
        = ∑ d, L h d := Finset.sum_congr rfl fun d _ => hone d
      _ = 1 := by simpa [tsum_fintype] using (L h).tsum_coe
  · rw [ite_eq_right heq]
    have hzero : ∀ d : D, L h d * posterior H D π L d h' = 0 := by
      intro d
      by_cases hd : L h d = 0
      · rw [hd, zero_mul]
      · rw [hpost d h' hd, ite_eq_right heq, mul_zero]
    calc ∑ d, L h d * posterior H D π L d h'
        = ∑ _d : D, (0 : ℝ≥0∞) := Finset.sum_congr rfl fun d _ => hzero d
      _ = 0 := Finset.sum_const_zero

/-- An identity transmission kernel leaves every distribution stationary. -/
theorem bind_eq_of_eq_pure (H : Type*) (K : H → PMF H)
    (hK : ∀ h, K h = PMF.pure h) (σ : PMF H) : σ.bind K = σ := by
  have hKK : K = PMF.pure := funext hK
  rw [hKK]
  exact PMF.bind_pure σ

end Cslib.MachineLearning.Bayesian.IteratedLearning
