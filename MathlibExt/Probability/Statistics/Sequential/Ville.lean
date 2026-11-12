/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import MathlibExt.Probability.SupermartingaleOptionalStopping

/-!
# Ville's maximal inequality

For a nonnegative real supermartingale `M` indexed by `ℕ` on a finite measure space and a
threshold `a > 0`, the event that the path ever reaches `a` satisfies
`a · μ{∃ n, a ≤ M n} ≤ E[M 0]`.

## Main statement

* `MeasureTheory.Supermartingale.ville_maximal_ineq`: the countable-time inequality. No
  martingale, normalization (`M 0 = 1`), integrable-supremum or uniform-integrability hypothesis
  is needed.

## Proof

At a finite horizon `N`, the hitting time of `[a, ∞)` before `N` is a bounded stopping time.
Markov's inequality and bounded optional stopping for supermartingales
(`Supermartingale.expected_stoppedValue_le`) bound the finite-horizon crossing event. The
finite-horizon events increase to the countable crossing event, and continuity of measure
passes to the limit.

Confidence sequences and e-processes are not covered here.

## References

* J. Ville, *Étude critique de la notion de collectif* (1939).
* R. Durrett, *Probability: Theory and Examples*, 5th ed., Exercise 4.8.2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace MeasureTheory

/-- **Ville's maximal inequality** (countable time). For a nonnegative real supermartingale `M`
on a finite measure space and `a > 0`, the measure of the event that the path ever reaches `a`
satisfies `a · μ{∃ n, a ≤ M n} ≤ E[M 0]`. No martingale, normalization, integrable-supremum or
uniform-integrability hypothesis is needed.

Source: J. Ville, *Étude critique de la notion de collectif* (1939); Durrett, *Probability:
Theory and Examples*, 5th ed., Exercise 4.8.2. -/
theorem Supermartingale.ville_maximal_ineq
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hsup : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) {a : ℝ} (ha : 0 < a) :
    a * μ.real {ω | ∃ n, a ≤ M n ω} ≤ ∫ ω, M 0 ω ∂μ := by
  have hfin (N : ℕ) : a * μ.real {ω | ∃ n ≤ N, a ≤ M n ω} ≤ ∫ ω, M 0 ω ∂μ := by
    set τ : Ω → WithTop ℕ := fun ω => (hittingBtwn M (Set.Ici a) 0 N ω : ℕ)
    have hτ : IsStoppingTime 𝒢 τ :=
      hsup.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hbdd (ω : Ω) : τ ω ≤ N := WithTop.coe_le_coe.2 (hittingBtwn_le ω)
    calc a * μ.real {ω | ∃ n ≤ N, a ≤ M n ω}
        ≤ a * μ.real {ω | a ≤ stoppedValue M τ ω} := by
          refine mul_le_mul_of_nonneg_left (measureReal_mono ?_) ha.le
          rintro ω ⟨n, hn, h⟩
          exact stoppedValue_hittingBtwn_mem ⟨n, ⟨Nat.zero_le n, hn⟩, h⟩
      _ ≤ ∫ ω, stoppedValue M τ ω ∂μ :=
          mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => hnonneg _ ω)
            (integrable_stoppedValue ℕ hτ hsup.integrable hbdd) a
      _ ≤ ∫ ω, M 0 ω ∂μ := hsup.expected_stoppedValue_le hτ hbdd
  have hmono : Monotone fun N : ℕ => {ω | ∃ n ≤ N, a ≤ M n ω} := by
    rintro N N' hNN' ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hNN', h⟩
  have hunion : ⋃ N : ℕ, {ω | ∃ n ≤ N, a ≤ M n ω} = {ω | ∃ n, a ≤ M n ω} := by
    ext ω
    refine ⟨fun hω => ?_, fun ⟨n, h⟩ => Set.mem_iUnion.2 ⟨n, n, le_rfl, h⟩⟩
    obtain ⟨-, n, -, h⟩ := Set.mem_iUnion.1 hω
    exact ⟨n, h⟩
  have htend : Tendsto (fun N : ℕ => μ.real {ω | ∃ n ≤ N, a ≤ M n ω}) atTop
      (nhds (μ.real {ω | ∃ n, a ≤ M n ω})) := by
    rw [← hunion]
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hmono)
  exact le_of_tendsto' (htend.const_mul a) hfin

end MeasureTheory
