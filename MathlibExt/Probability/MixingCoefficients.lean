/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real

/-!
# Mixing coefficients

Bradley's inequality bounds each joint-probability discrepancy by half a uniform bound on
conditional-probability deviations over past and future events.
-/

open MeasureTheory

namespace MetaMathlibExt

-- The coefficient is indexed by positive lags, although the bound holds for any lag.
set_option linter.unusedVariables false in
/-- **Bradley's inequality between the $\alpha$- and $\varphi$-mixing coefficients.** Let
$(X_j)_{j \ge 1}$ be random variables on a probability space $(\Omega, \mathbb{P})$ with values in
a measurable space, and let $k \ge 1$. Suppose a real number $c$ bounds every term defining the
$\varphi$-mixing coefficient $\varphi(k)$: for every $p \ge 1$, every event
$A \in \sigma(X_j : 1 \le j \le p)$ with $\mathbb{P}(A) > 0$ and every event
$B \in \sigma(X_j : j \ge k + p)$, $|\mathbb{P}(B \mid A) - \mathbb{P}(B)| \le c$. Then $c/2$
bounds every term defining the $\alpha$-mixing coefficient $\alpha(k)$: for every $p \ge 1$,
every event $A \in \sigma(X_j : 1 \le j \le p)$ and every event $B \in \sigma(X_j : j \ge k + p)$,
$|\mathbb{P}(A \cap B) - \mathbb{P}(A)\mathbb{P}(B)| \le c/2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 18 (Bradley) (`jis-2024-24.3.2-prop-18`). -/
public theorem alpha_mixing_le_half_phi_mixing {Ω β : Type*} [MeasurableSpace Ω]
    [mβ : MeasurableSpace β] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → β)
    (hX : ∀ j, Measurable (X j)) {k : ℕ} (hk : 1 ≤ k) (c : ℝ)
    (hc : ∀ p, 1 ≤ p → ∀ A B : Set Ω,
      MeasurableSet[⨆ j ∈ Finset.Icc 1 p, mβ.comap (X j)] A →
      MeasurableSet[⨆ (j : ℕ) (_ : k + p ≤ j), mβ.comap (X j)] B → μ A ≠ 0 →
      |(ProbabilityTheory.cond μ A B).toReal - (μ B).toReal| ≤ c)
    {p : ℕ} (hp : 1 ≤ p) {A B : Set Ω}
    (hA : MeasurableSet[⨆ j ∈ Finset.Icc 1 p, mβ.comap (X j)] A)
    (hB : MeasurableSet[⨆ (j : ℕ) (_ : k + p ≤ j), mβ.comap (X j)] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ c / 2 := by
  have hpast : (⨆ j ∈ Finset.Icc 1 p, mβ.comap (X j)) ≤ ‹MeasurableSpace Ω› :=
    iSup_le fun j => iSup_le fun _ => (hX j).comap_le
  -- Bound the discrepancy for any past event by its probability times c.
  have bound (S : Set Ω) (hS : MeasurableSet[⨆ j ∈ Finset.Icc 1 p, mβ.comap (X j)] S) :
      |μ.real (S ∩ B) - μ.real S * μ.real B| ≤ μ.real S * c := by
    by_cases hzero : μ S = 0
    · simp [Measure.real, hzero, measure_mono_null Set.inter_subset_left hzero]
    have hmul := ProbabilityTheory.cond_mul_eq_inter (hpast S hS) B μ
    simp only [Measure.real]
    rw [← hmul, ENNReal.toReal_mul, mul_comm, ← mul_sub, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hc p hp S B hS hB hzero) ENNReal.toReal_nonneg
  -- Complementing A negates the discrepancy, so the two bounds can be added.
  have hAm := hpast A hA
  have hpartition : μ.real (A ∩ B) + μ.real (Aᶜ ∩ B) = μ.real B := by
    simpa only [Set.sdiff_eq, Set.inter_comm B] using
      (measureReal_inter_add_sdiff (μ := μ) (s := B) hAm)
  have hcompl : μ.real (Aᶜ ∩ B) - μ.real Aᶜ * μ.real B =
      -(μ.real (A ∩ B) - μ.real A * μ.real B) := by
    rw [probReal_compl_eq_one_sub hAm]
    linarith only [hpartition]
  have hboth := add_le_add (bound A hA) (bound Aᶜ hA.compl)
  rw [hcompl, abs_neg, probReal_compl_eq_one_sub hAm] at hboth
  change |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ c / 2
  linarith only [hboth]

end MetaMathlibExt
