/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.JumpHold

open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

namespace MathlibExt.Probability.Process.EventJumpHold

@[expose] public section

/-!
# Finite-event JumpHold adapter

From event rates and successors over a finite event type, this module builds
the total rate, the holding rate (fictitious rate `1` exactly at zero total),
the normalized event distribution and the jump distribution obtained by
pushing the event distribution forward along successors (point mass at zero
total). Self-events are retained in totals and masses, and duplicate
successors sum. The adapter reuses the existing `JumpHold` chain directly:
the input law is `JumpHold.inputMeasure` applied to the jump PMF and the
path is `JumpHold.path` applied to the holding rate, with no alias
definitions. Observations are functions of that path and agree with the
corresponding jump-chain values on each holding interval. All statements are
about rates and jump distributions only. A stochastic reaction network is the
case whose events are its reactions and whose successors are its reaction
jumps: `StochasticCRN.totalRate`, `holdRate`, `reactionPMF` and `jumpPMF` are
these definitions applied to its propensities (they agree by `rfl`).
-/

/-- **Total event rate.** For a finite type of events `e` with real rates `rate e x`, the total
rate at a state `x` is `∑ e, rate e x`, summed over every event, events that leave `x` unchanged
included. -/
def totalRate {E S : Type*} [Fintype E] (rate : E → S → ℝ) (x : S) : ℝ :=
  ∑ e, rate e x

/-- **Holding rate.** The holding rate at a state `x` is the total event rate at `x` when it is
nonzero, and the fictitious rate `1` when it is zero. -/
noncomputable def holdRate {E S : Type*} [Fintype E] (rate : E → S → ℝ) (x : S) : ℝ :=
  if totalRate rate x = 0 then 1 else totalRate rate x

/-- **Positivity of the holding rate.** If every event rate is nonnegative, the holding rate is
positive at every state. -/
theorem holdRate_pos {E S : Type*} [Fintype E] (rate : E → S → ℝ)
    (h_nn : ∀ e x, 0 ≤ rate e x) (x : S) : 0 < holdRate rate x := by
  have h_fold : (∑ e, rate e x) = totalRate rate x := rfl
  have h_le : (0 : ℝ) ≤ totalRate rate x := by
    rw [← h_fold]
    exact Finset.sum_nonneg (fun e _ => h_nn e x)
  unfold holdRate
  by_cases h : totalRate rate x = 0
  · rw [ite_eq_left h]
    exact one_pos
  · rw [ite_eq_right h]
    exact lt_of_le_of_ne h_le (Ne.symm h)

/-- **Holding rate at zero total rate.** At a state whose total event rate is `0`, the holding
rate is `1`. -/
theorem holdRate_eq_one_of_totalRate_eq_zero {E S : Type*} [Fintype E]
    (rate : E → S → ℝ) (x : S) (h : totalRate rate x = 0) :
    holdRate rate x = 1 := by
  unfold holdRate
  exact ite_eq_left h

/-- **Holding rate at nonzero total rate.** At a state whose total event rate is nonzero, the
holding rate equals the total event rate. -/
theorem holdRate_eq_totalRate_of_totalRate_ne_zero {E S : Type*} [Fintype E]
    (rate : E → S → ℝ) (x : S) (h : totalRate rate x ≠ 0) :
    holdRate rate x = totalRate rate x := by
  unfold holdRate
  exact ite_eq_right h

/-- **Event distribution.** For nonnegative event rates and a state `x` whose total rate
`λ(x) = ∑ e, rate e x` is nonzero, the probability distribution on the events that gives each
event `e` the probability `rate e x / λ(x)`. -/
noncomputable def eventPMF {E S : Type*} [Fintype E] (rate : E → S → ℝ)
    (h_nn : ∀ e x, 0 ≤ rate e x) (x : S) (h : totalRate rate x ≠ 0) : PMF E :=
  PMF.ofFintype (fun e => ENNReal.ofReal (rate e x / totalRate rate x)) (by
    have h_fold : (∑ e, rate e x) = totalRate rate x := rfl
    have h_le : (0 : ℝ) ≤ totalRate rate x := by
      rw [← h_fold]
      exact Finset.sum_nonneg (fun e _ => h_nn e x)
    have hpos : 0 < totalRate rate x := lt_of_le_of_ne h_le (Ne.symm h)
    have h_w : ∀ e ∈ Finset.univ, 0 ≤ rate e x / totalRate rate x :=
      fun e _ => div_nonneg (h_nn e x) (le_of_lt hpos)
    have h_sum : (∑ e, rate e x / totalRate rate x) = 1 := by
      rw [← Finset.sum_div, h_fold, div_self h]
    calc ∑ e, ENNReal.ofReal (rate e x / totalRate rate x)
        = ENNReal.ofReal (∑ e, rate e x / totalRate rate x) :=
          (ENNReal.ofReal_sum_of_nonneg h_w).symm
      _ = 1 := by rw [h_sum, ENNReal.ofReal_one])

/-- **Jump distribution.** For nonnegative event rates and successors `succ e x` (the state after
event `e` occurs at `x`), the law of the next state from `x`: if the total rate at `x` is
nonzero, the image of the event distribution under `e ↦ succ e x`; if it is zero, the point
mass at `x`. -/
noncomputable def jumpPMF {E S : Type*} [Fintype E] (rate : E → S → ℝ)
    (succ : E → S → S) (h_nn : ∀ e x, 0 ≤ rate e x) (x : S) : PMF S :=
  if h : totalRate rate x = 0 then PMF.pure x
  else (eventPMF rate h_nn x h).map (fun e => succ e x)

/-- **Point masses of the jump distribution.** For nonnegative event rates and a state `x` with
nonzero total rate `λ(x)`, the jump distribution from `x` gives each state `y` the probability
`(∑ e ∈ {e | succ e x = y}, rate e x) / λ(x)`: events with the same successor add up, and
events that leave `x` unchanged count towards `y = x`. -/
theorem jumpPMF_apply_of_totalRate_ne_zero {E S : Type*} [Fintype E] [DecidableEq S]
    (rate : E → S → ℝ) (succ : E → S → S) (h_nn : ∀ e x, 0 ≤ rate e x)
    (x : S) (h : totalRate rate x ≠ 0) (y : S) :
    jumpPMF rate succ h_nn x y =
      ENNReal.ofReal
        ((∑ e ∈ Finset.univ.filter (fun e => succ e x = y), rate e x) /
          totalRate rate x) := by
  have h_fold : (∑ e, rate e x) = totalRate rate x := rfl
  have h_le : (0 : ℝ) ≤ totalRate rate x := by
    rw [← h_fold]
    exact Finset.sum_nonneg (fun e _ => h_nn e x)
  have hpos : 0 < totalRate rate x := lt_of_le_of_ne h_le (Ne.symm h)
  have h_w : ∀ e ∈ Finset.univ.filter (fun e => succ e x = y),
      0 ≤ rate e x / totalRate rate x :=
    fun e _ => div_nonneg (h_nn e x) (le_of_lt hpos)
  unfold jumpPMF
  rw [dite_eq_right h]
  simp only [PMF.map_apply, eventPMF, PMF.ofFintype_apply, tsum_fintype]
  trans ∑ a, if succ a x = y then ENNReal.ofReal (rate a x / totalRate rate x)
    else 0
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : succ a x = y
    · rw [ite_eq_left ha.symm, ite_eq_left ha]
    · rw [ite_eq_right (Ne.symm ha), ite_eq_right ha]
  · rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg h_w, ← Finset.sum_div]

/-- **Jump distribution at zero total rate.** At a state `x` whose total event rate is `0`, the
jump distribution from `x` is the point mass at `x`. -/
theorem jumpPMF_eq_pure_of_totalRate_eq_zero {E S : Type*} [Fintype E]
    (rate : E → S → ℝ) (succ : E → S → S) (h_nn : ∀ e x, 0 ≤ rate e x)
    (x : S) (h : totalRate rate x = 0) : jumpPMF rate succ h_nn x = PMF.pure x := by
  unfold jumpPMF
  exact dite_eq_left h

/-- **Grouped event rates.** For nonnegative event rates and a state `x` with nonzero total rate,
the holding rate at `x` times the probability that the jump distribution from `x` gives a state
`y` is `∑ e ∈ {e | succ e x = y}, rate e x`, the total rate of the events leading to `y`. -/
theorem holdRate_mul_jumpPMF_toReal_of_totalRate_ne_zero {E S : Type*} [Fintype E]
    [DecidableEq S] (rate : E → S → ℝ) (succ : E → S → S)
    (h_nn : ∀ e x, 0 ≤ rate e x) (x : S) (h : totalRate rate x ≠ 0) (y : S) :
    holdRate rate x * (jumpPMF rate succ h_nn x y).toReal =
      ∑ e ∈ Finset.univ.filter (fun e => succ e x = y), rate e x := by
  have h_fold : (∑ e, rate e x) = totalRate rate x := rfl
  have h_le : (0 : ℝ) ≤ totalRate rate x := by
    rw [← h_fold]
    exact Finset.sum_nonneg (fun e _ => h_nn e x)
  have hpos : 0 < totalRate rate x := lt_of_le_of_ne h_le (Ne.symm h)
  have hqr : 0 ≤ (∑ e ∈ Finset.univ.filter (fun e => succ e x = y), rate e x) /
      totalRate rate x :=
    div_nonneg (Finset.sum_nonneg (fun e _ => h_nn e x)) (le_of_lt hpos)
  rw [jumpPMF_apply_of_totalRate_ne_zero rate succ h_nn x h y,
    ENNReal.toReal_ofReal hqr, holdRate_eq_totalRate_of_totalRate_ne_zero rate x h,
    mul_comm, div_mul_cancel₀ _ h]

/-- **Observations on a holding interval.** Assume every event rate is nonnegative, and run the
jump–hold chain from `x₀` with the holding rate on a step sequence `ω` whose clocks `(ω j).2`
are nonnegative. If `T k ≤ s < T (k + 1)` for its jump times `T`, then any observation `f` of
its path at time `s` equals `f` of the `k`-th state of its jump chain. -/
theorem obs_path_eq_obs_chain_of_le_of_lt {E S β : Type*} [Fintype E]
    (rate : E → S → ℝ) (h_nn : ∀ e x, 0 ≤ rate e x) (f : S → β) (x₀ : S)
    (ω : ℕ → (S → S) × ℝ) (h_clock : ∀ j, 0 ≤ (ω j).2) (k : ℕ) (s : ℝ)
    (h_lo : JumpHold.jumpTime (holdRate rate) x₀ ω k ≤ s)
    (h_hi : s < JumpHold.jumpTime (holdRate rate) x₀ ω (k + 1)) :
    f (JumpHold.path (holdRate rate) x₀ ω s) =
      f (ProbabilityTheory.ctmcJumpChain x₀ ω k) := by
  exact congrArg f
    (JumpHold.path_eq_ctmcJumpChain (holdRate_pos rate h_nn) h_clock h_lo h_hi)

end

end MathlibExt.Probability.Process.EventJumpHold
