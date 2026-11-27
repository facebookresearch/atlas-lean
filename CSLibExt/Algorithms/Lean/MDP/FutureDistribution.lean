/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.StochasticShortestPath
public import Mathlib.Basic.ENNReal.Real

/-! # Future-distribution concentration for finite Markov decision processes -/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal

namespace Cslib.Algorithms.Lean.MarkovDecision

open Convexity

variable {S A : Type*} [Fintype S]

/-- Evolve the initial state distribution `ν` through the ordered deterministic decision rules
`π`. The row vector is multiplied on the right, in chronological order. -/
noncomputable def futureStateWeights (M : MDP S A ℝ) (ν : StdSimplex ℝ S) :
    (m : ℕ) → (Fin m → S → A) → S → ℝ
  | 0, _ => fun y => ν.weights y
  | m + 1, π =>
      futureStateWeights M ν m (fun i => π i.castSucc) ᵥ* transitionMatrix M (π (Fin.last m))

/-- For a stochastic MDP the propagated weights are nonnegative and have total mass one. -/
theorem futureStateWeights_stochastic {M : MDP S A ℝ} (hM : M.Stochastic)
    (ν : StdSimplex ℝ S) (m : ℕ) (π : Fin m → S → A) :
    (∀ y, 0 ≤ futureStateWeights M ν m π y) ∧ ∑ y, futureStateWeights M ν m π y = 1 := by
  induction m with
  | zero => exact ⟨ν.weights_nonneg, ν.total_of_fintype⟩
  | succ m ih =>
    let ω := futureStateWeights M ν m (fun i => π i.castSucc)
    let a := π (Fin.last m)
    obtain ⟨hn, hs⟩ := ih (fun i => π i.castSucc)
    have h (y : S) : futureStateWeights M ν (m + 1) π y = ∑ x, ω x * M.prob x (a x) y :=
      rfl
    simp only [h]
    constructor
    · exact fun y => Finset.sum_nonneg fun x _ => mul_nonneg (hn x) (hM.1 x (a x) y)
    · rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hM.2, mul_one]
      exact hs

/-- The extended nonnegative ratio of a propagated state weight to its reference weight.
For valid probability weights this is the ordinary ratio at a positive reference weight;
`0 / 0 = 0`, and positive weight divided by zero is infinity. Both real weights are mapped
by `ENNReal.ofReal`, which sends negative inputs to zero. -/
noncomputable def futureWeightRatio (p q : ℝ) : ℝ≥0∞ := ENNReal.ofReal p / ENNReal.ofReal q

@[simp]
theorem futureWeightRatio_zero_left (q : ℝ) : futureWeightRatio 0 q = 0 := by
  simp [futureWeightRatio]

@[simp]
theorem futureWeightRatio_zero_right_of_pos {p : ℝ} (hp : 0 < p) :
    futureWeightRatio p 0 = ∞ := by
  rw [futureWeightRatio, ENNReal.ofReal_zero, ENNReal.div_zero (ENNReal.ofReal_ne_zero_iff.mpr hp)]

theorem futureWeightRatio_of_pos {p q : ℝ} (hq : 0 < q) :
    futureWeightRatio p q = ENNReal.ofReal (p / q) :=
  (ENNReal.ofReal_div_of_pos hq).symm

/-- **Future-distribution concentration coefficient.** At positive `m`, take the supremum
of the extended nonnegative weight ratios over every length-`m` sequence of deterministic
rules and every destination state. At `m = 0` the coefficient is `1`, independently of `ν` and `μ`.

The definition itself assumes neither stochastic transitions nor finite nonempty actions.
For a stochastic MDP, `futureStateWeights_stochastic` shows that the propagated weights are
probability masses. For finite nonempty state and action types,
`exists_futureWeightRatio_eq_coefficient` shows that the positive-time supremum is attained.

Source: R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*,
SIAM J. Control Optim. 46(2), 2007, §5.1, Definition 5.1 and equation (5.1). -/
noncomputable def futureDistributionCoefficient (M : MDP S A ℝ)
    (ν μ : StdSimplex ℝ S) : ℕ → ℝ≥0∞
  | 0 => 1
  | m + 1 => ⨆ z : (Fin (m + 1) → S → A) × S,
      futureWeightRatio (futureStateWeights M ν (m + 1) z.1 z.2) (μ.weights z.2)

@[simp]
theorem futureDistributionCoefficient_zero (M : MDP S A ℝ) (ν μ : StdSimplex ℝ S) :
    futureDistributionCoefficient M ν μ 0 = 1 := rfl

/-- Each sequence of rules and each destination gives a lower bound on the coefficient
at a positive horizon. -/
theorem futureWeightRatio_le_coefficient (M : MDP S A ℝ) (ν μ : StdSimplex ℝ S)
    (m : ℕ) (π : Fin (m + 1) → S → A) (y : S) :
    futureWeightRatio (futureStateWeights M ν (m + 1) π y) (μ.weights y) ≤
      futureDistributionCoefficient M ν μ (m + 1) :=
  le_iSup (fun z : (Fin (m + 1) → S → A) × S =>
    futureWeightRatio (futureStateWeights M ν (m + 1) z.1 z.2) (μ.weights z.2)) (π, y)

/-- At a positive horizon with finite nonempty states and actions, a sequence of rules
and a destination attain the coefficient, including when it is infinite. -/
theorem exists_futureWeightRatio_eq_coefficient [Finite A] [Nonempty A] [Nonempty S]
    (M : MDP S A ℝ) (ν μ : StdSimplex ℝ S) (m : ℕ) :
    ∃ (π : Fin (m + 1) → S → A) (y : S),
      futureWeightRatio (futureStateWeights M ν (m + 1) π y) (μ.weights y) =
        futureDistributionCoefficient M ν μ (m + 1) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let f := fun z : (Fin (m + 1) → S → A) × S =>
    futureWeightRatio (futureStateWeights M ν (m + 1) z.1 z.2) (μ.weights z.2)
  obtain ⟨⟨π, y⟩, _, h⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
  rw [Finset.sup_univ_eq_iSup] at h
  exact ⟨π, y, h.symm⟩

end Cslib.Algorithms.Lean.MarkovDecision
