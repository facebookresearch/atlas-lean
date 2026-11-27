/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-! # Transition concentration for Markov decision processes -/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace Cslib.Algorithms.Lean.MarkovDecision

open Convexity

variable {S A : Type*}

/-- **Transition concentration coefficient.** The supremum of the extended nonnegative ratios
`p(s, a, y) / μ(y)` over source states `s`, actions `a`, and destination states `y`, where `μ`
is the reference probability vector. The ratio uses `ENNReal.ofReal` on both weights, so it
agrees with the usual nonnegative ratio for stochastic transitions: `0 / 0 = 0`, and a
positive transition weight divided by zero is infinity. Negative transition weights, which
are excluded on the stochastic domain, are sent to zero. The definition itself assumes neither
stochasticity nor finiteness; the supremum is attained for finite nonempty states and actions.

Source: R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*,
SIAM J. Control Optim. 46(2), 2007, §5.1, Definition 5.1. -/
noncomputable def transitionConcentrationCoefficient (M : MDP S A ℝ)
    (μ : StdSimplex ℝ S) : ℝ≥0∞ :=
  ⨆ z : S × A × S, ENNReal.ofReal (M.prob z.1 z.2.1 z.2.2) / ENNReal.ofReal (μ.weights z.2.2)

/-- A bound on the coefficient is equivalent to the same bound on every transition ratio. -/
theorem transitionConcentrationCoefficient_le_iff (M : MDP S A ℝ) (μ : StdSimplex ℝ S)
    (b : ℝ≥0∞) : transitionConcentrationCoefficient M μ ≤ b ↔
      ∀ s a y, ENNReal.ofReal (M.prob s a y) / ENNReal.ofReal (μ.weights y) ≤ b := by
  unfold transitionConcentrationCoefficient
  rw [iSup_le_iff]
  exact ⟨fun h s a y => h (s, a, y), fun h z => h z.1 z.2.1 z.2.2⟩

/-- For finite nonempty state and action types, a transition attains the coefficient. -/
theorem exists_transitionRatio_eq_coefficient [Finite S] [Finite A] [Nonempty S] [Nonempty A]
    (M : MDP S A ℝ) (μ : StdSimplex ℝ S) :
    ∃ s a y, ENNReal.ofReal (M.prob s a y) / ENNReal.ofReal (μ.weights y) =
      transitionConcentrationCoefficient M μ := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  let _ : Fintype A := Fintype.ofFinite A
  let f := fun z : S × A × S =>
    ENNReal.ofReal (M.prob z.1 z.2.1 z.2.2) / ENNReal.ofReal (μ.weights z.2.2)
  obtain ⟨⟨s, a, y⟩, _, h⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
  refine ⟨s, a, y, le_antisymm (le_iSup f (s, a, y)) ?_⟩
  change iSup f ≤ f (s, a, y)
  rw [← h]
  exact iSup_le fun z => Finset.le_sup (Finset.mem_univ z)

/-- On finite nonempty types the coefficient is infinite exactly when some positive transition
lands outside the support of the reference distribution. -/
theorem transitionConcentrationCoefficient_eq_top_iff
    [Finite S] [Finite A] [Nonempty S] [Nonempty A] (M : MDP S A ℝ) (μ : StdSimplex ℝ S) :
    transitionConcentrationCoefficient M μ = ∞ ↔
      ∃ s a y, 0 < M.prob s a y ∧ μ.weights y = 0 := by
  constructor
  · intro h
    obtain ⟨s, a, y, hy⟩ := exists_transitionRatio_eq_coefficient M μ
    rw [h, ENNReal.div_eq_top] at hy
    rcases hy with hy | hy
    · exact ⟨s, a, y, ENNReal.ofReal_ne_zero_iff.mp hy.1,
        le_antisymm (ENNReal.ofReal_eq_zero.mp hy.2) (μ.weights_nonneg y)⟩
    · exact (ENNReal.ofReal_lt_top.ne hy.1).elim
  · rintro ⟨s, a, y, hp, hμ⟩
    have h := (transitionConcentrationCoefficient_le_iff M μ
      (transitionConcentrationCoefficient M μ)).mp le_rfl s a y
    rw [hμ, ENNReal.ofReal_zero, ENNReal.div_zero (ENNReal.ofReal_ne_zero_iff.mpr hp)] at h
    exact top_unique h

end Cslib.Algorithms.Lean.MarkovDecision
