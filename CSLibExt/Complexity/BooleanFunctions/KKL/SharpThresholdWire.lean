/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.HCTensorLib
public import MathlibExt.Probability.Hypercontractivity.PBiasedHCLib

@[expose] public section

/-!
# Wiring the sharp-threshold argument: exponent ranges and the remaining goal

The master estimate's `q`-value, the fact that the forward exponent range `[2, 4]` and
the master range `(1, 2]` meet only at `2` (`stw_ranges_meet_only_at_two`), the variance
coefficient gap (equality iff `p = 1/2`), and the conditional chain from the remaining
goal `stw_RemainingGoal` (which is exactly `∀ p ∈ (1/2, q), PBiasedHCLib p`) to
rho-optimise and sharp threshold. Status: the remaining goal is refuted for `q > 9/10`
(`dtpc_remainingGoal_false`); it holds for the empty window `q ≤ 1/2`
(`stw_RemainingGoal_empty_window`). The final verdict `stw_verdict` combines the pieces.

## Main definitions

* `stw_RemainingGoal`: the remaining goal over a window `(1/2, q)`, definitionally
  `∀ p ∈ Ioo (1/2) q, PBiasedHCLib p`; false for `q > 9/10`.

## Main results

* `stw_ranges_meet_only_at_two`, `stw_variance_coeff_gap`,
  `stw_coeff_gap_eq_iff_half`: exponent and coefficient gap computations.
* `stw_rhoOptimise_of_lib`, `stw_sharpThreshold_of_lib`: the conditional chain.
* `stw_verdict`: the combined verdict.
-/


open scoped BigOperators
open Finset
open Real Set
open StatMech StatMech.OSSS

set_option linter.style.longLine false

namespace StatMech.Probability

theorem stw_master_q_value {u : ℝ} (ρ : ℝ) (hρsq : ρ ^ 2 = 1 - u) :
    (1 + ρ ^ 2 : ℝ) = 2 - u := by
  rw [hρsq]; ring

theorem stw_master_uses_exponent_le_two {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 < 2 - u ∧ 2 - u ≤ 2 := ⟨by linarith, by linarith⟩

/-- The forward exponent range `[2, 4]` and the master range `(1, 2]` meet only
at `2`. -/
theorem stw_ranges_meet_only_at_two {q : ℝ} (hfwd : 2 ≤ q ∧ q ≤ 4) (hmaster : 1 < q ∧ q ≤ 2) :
    q = 2 := le_antisymm hmaster.2 hfwd.1

theorem stw_variance_coeff_gap {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    4 * p ^ 2 * (1 - p) ^ 2 ≤ p * (1 - p) := by
  nlinarith [mul_nonneg hp0 (by linarith : (0:ℝ) ≤ 1 - p), sq_nonneg (1 - 2 * p),
    mul_nonneg (mul_nonneg hp0 (by linarith : (0:ℝ) ≤ 1 - p)) (sq_nonneg (1 - 2 * p))]

theorem stw_coeff_gap_eq_iff_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * p ^ 2 * (1 - p) ^ 2 = p * (1 - p) ↔ p = 1 / 2 := by
  constructor
  · intro h
    have hpos : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
    have hfac : p * (1 - p) * (1 - 4 * p * (1 - p)) = 0 := by nlinarith [h]
    have h4 : 1 - 4 * p * (1 - p) = 0 := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact absurd h' (ne_of_gt hpos)
      · exact h'
    have hsq : (1 - 2 * p) ^ 2 = 0 := by nlinarith [h4]
    have : 1 - 2 * p = 0 := by nlinarith [sq_nonneg (1 - 2 * p), hsq]
    linarith
  · intro h; rw [h]; norm_num

theorem stw_pbiasedHCLib_implies_proved_lhs {p ρ u v : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((1 - p) * u + p * v) ^ 2 + (ρ ^ 2 + 1 - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2
      ≤ ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2 := by
  have hgap := stw_variance_coeff_gap hp0 hp1
  nlinarith [sq_nonneg (u - v), sq_nonneg ρ,
    mul_nonneg (sq_nonneg ρ) (sq_nonneg (u - v)),
    mul_nonneg (mul_nonneg (sq_nonneg ρ) (by linarith [hgap] : (0:ℝ) ≤ p * (1 - p) - 4 * p ^ 2 * (1 - p) ^ 2)) (sq_nonneg (u - v))]

theorem stw_kkl_logGain_half {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (φ : ConfigSpace ι → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  htl_kkl_logGain_half φ

/-- The remaining goal over a window `(1/2, q)`: definitionally
`∀ p ∈ Ioo (1/2) q, PBiasedHCLib p`. False for `q > 9/10`
(`dtpc_remainingGoal_false`); holds for the empty window `q ≤ 1/2`. -/
def stw_RemainingGoal (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p

theorem stw_rhoOptimise_of_lib {q : ℝ} (H : stw_RemainingGoal q) :
    ptn_RhoOptimise q :=
  htl_rhoOptimise_of_lib H

theorem stw_sharpThreshold_of_lib {q : ℝ} (hq1 : q ≤ 1)
    (H : stw_RemainingGoal q)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  htl_sharpThreshold hq1 H A hA hq hv0 hL hhalf hvar hLL'

theorem stw_RemainingGoal_empty_window {q : ℝ} (hq : q ≤ 1 / 2) : stw_RemainingGoal q := by
  intro p hp
  exact absurd (lt_trans hp.1 hp.2) (by linarith [hq] : ¬ (1 / 2 : ℝ) < q)

theorem stw_verdict {u p : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hne : p ≠ 1 / 2) :
    (1 < 2 - u ∧ 2 - u ≤ 2) ∧ (4 * p ^ 2 * (1 - p) ^ 2 < p * (1 - p)) := by
  refine ⟨stw_master_uses_exponent_le_two hu0 hu1, ?_⟩
  rcases lt_or_ge (4 * p ^ 2 * (1 - p) ^ 2) (p * (1 - p)) with h | h
  · exact h
  · exact absurd (le_antisymm (stw_variance_coeff_gap hp0.le hp1.le) h)
      (fun heq => hne ((stw_coeff_gap_eq_iff_half hp0 hp1).mp heq))

end StatMech.Probability
