/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.AugmentedAdjoint
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Augmented-state backpropagation tests

Closed checks: zero horizon (the total cost is `b + ellN`, so the
gradient is `∇ ellN + ∇ b`), the one-step cost identity, the
counterexample showing the lift pullback `∇ b x` cannot be dropped,
and a linear case where the backward pass vanishes and the gradient
is exactly `∇ b x`. The scalar witness numbers are checked as real
arithmetic: `J(1) = 1`, `J'(1) = 3` for `J(t) = t^2/2 + t^4/2`.
-/

namespace Cslib.MachineLearning.AugmentedAdjoint

open InnerProductSpace
open scoped Gradient

-- Zero horizon: the backward pass is `∇ ellN x`, and the corrected
-- theorem gives `∇ (b + ellN) x = ∇ ellN x + ∇ b x`.
example {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → ℝ) (ellN : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hb : DifferentiableAt ℝ b x)
    (hellN : DifferentiableAt ℝ ellN x) :
    ∇ (fun y => augFinalLoss ellN (augForward M ell 0 (augLift b y))) x =
      ∇ ellN x + ∇ b x := by
  have h := aug_gradient_eq_backward M ell b ellN x 0
    (fun k hk => (Nat.not_lt_zero k hk).elim)
    (fun k hk => (Nat.not_lt_zero k hk).elim) hb hellN
  rwa [show augBackward M ell ellN 0 x = ∇ ellN x from rfl] at h

-- One step: the total cost is `b x + ell 0 x + ellN (M 0 x)`.
example {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → ℝ) (ellN : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    augFinalLoss ellN (augForward M ell 1 (augLift b x)) =
      b x + ell 0 x + ellN (M 0 x) := by
  have h := aug_totalCost_eq M ell b ellN x 1
  simp only [Finset.sum_range_one] at h
  rw [show augTraj M x (0 : ℕ) = x from rfl,
    show augTraj M x 1 = M 0 x from rfl] at h
  exact h

-- The lift pullback cannot be dropped: at horizon `0` the uncorrected
-- statement would claim `∇ (b + ellN) x = ∇ ellN x` for every `b`,
-- which is false for a nonzero linear initial cost.
example :
    ∃ (b : EuclideanSpace ℝ (Fin 1) → ℝ) (x : EuclideanSpace ℝ (Fin 1)),
      (∀ k < (0 : ℕ), DifferentiableAt ℝ ((fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) k)
        (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) x k)) ∧
      (∀ k < (0 : ℕ), DifferentiableAt ℝ ((fun _ _ => (0 : ℝ)) k)
        (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) x k)) ∧
      DifferentiableAt ℝ b x ∧
      DifferentiableAt ℝ (fun _ => (0 : ℝ))
        (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) x 0) ∧
      ∇ (fun y => augFinalLoss (fun _ => (0 : ℝ))
        (augForward (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) (fun _ _ => (0 : ℝ)) 0
          (augLift b y))) x ≠
        augBackward (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) (fun _ _ => (0 : ℝ))
          (fun _ => (0 : ℝ)) 0 x := by
  obtain ⟨e, he⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 1))
  have hvacM : ∀ k < (0 : ℕ), DifferentiableAt ℝ ((fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) k)
      (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) 0 k) :=
    fun k hk => (Nat.not_lt_zero k hk).elim
  have hvacEll : ∀ k < (0 : ℕ), DifferentiableAt ℝ ((fun _ _ => (0 : ℝ)) k)
      (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) 0 k) :=
    fun k hk => (Nat.not_lt_zero k hk).elim
  have hellN0 : DifferentiableAt ℝ (fun _ => (0 : ℝ))
      (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) 0 0) :=
    differentiableAt_const 0
  have hFb0 : HasFDerivAt ⇑((innerSL ℝ) e) ((innerSL ℝ) e) 0 :=
    ((innerSL ℝ) e).hasFDerivAt
  rw [coe_innerSL_apply] at hFb0
  have hdiff : DifferentiableAt ℝ (fun y => ⟪e, y⟫_ℝ) 0 := hFb0.differentiableAt
  have hfd : fderiv ℝ (fun y => ⟪e, y⟫_ℝ) 0 = (innerSL ℝ) e := hFb0.fderiv
  have hgrad_ne : ∇ (fun y => ⟪e, y⟫_ℝ) 0 ≠ 0 := by
    intro hcon
    have h1 : ⟪∇ (fun y => ⟪e, y⟫_ℝ) 0, e⟫_ℝ = ⟪e, e⟫_ℝ := by
      rw [inner_gradient_left, hfd]
      exact innerSL_apply_apply ℝ e e
    rw [hcon] at h1
    simp only [inner_zero_left] at h1
    exact (inner_self_ne_zero.mpr he) h1.symm
  refine ⟨fun y => ⟪e, y⟫_ℝ, 0, hvacM, hvacEll, hdiff, hellN0, ?_⟩
  have hfun : (fun y => augFinalLoss (fun _ => (0 : ℝ))
        (augForward (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) (fun _ _ => (0 : ℝ)) 0
          (augLift (fun y => ⟪e, y⟫_ℝ) y)))
      = (fun y => ⟪e, y⟫_ℝ) := by
    funext y
    simp [augForward, augLift, augFinalLoss]
  have hRHS : augBackward (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1)))
      (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 0
      = (0 : EuclideanSpace ℝ (Fin 1)) := by
    have hrfl : augBackward (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1)))
        (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 0
        = ∇ (fun _ => (0 : ℝ))
          (augTraj (fun _ _ => (0 : EuclideanSpace ℝ (Fin 1))) 0 0) := rfl
    rw [hrfl]
    exact (hasGradientAt_const _ _).gradient
  rw [hfun, hRHS]
  exact hgrad_ne

-- Linear case: identity dynamics and zero losses at horizon `1` make
-- the backward pass vanish, so the gradient is exactly `∇ b x`.
example {d : ℕ} (b : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hb : DifferentiableAt ℝ b x) :
    ∇ (fun y => augFinalLoss (fun _ => (0 : ℝ))
      (augForward (fun _ => id) (fun _ _ => (0 : ℝ)) 1 (augLift b y))) x = ∇ b x := by
  have h := aug_gradient_eq_backward (fun _ => (id : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))) (fun _ _ => (0 : ℝ)) b (fun _ => (0 : ℝ)) x 1
    (fun k _ => differentiableAt_id)
    (fun k _ => differentiableAt_const _)
    hb (differentiableAt_const _)
  have hzero : augBackward (fun _ => (id : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))) (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 1 x = 0 := by
    simp [augBackward, augBack, augBackStep, fderiv_id]
  rw [hzero, zero_add] at h
  exact h

-- Scalar witness numbers: `J(t) = t^2/2 + t^4/2`, `J(1) = 1`, `J'(1) = 3`.
example : (1 : ℝ) ^ 2 / 2 + (1 : ℝ) ^ 4 / 2 = 1 := by norm_num

example : deriv (fun t : ℝ => t ^ 2 / 2 + t ^ 4 / 2) 1 = 3 := by
  have a : HasDerivAt (fun t : ℝ => t ^ 2 / 2) 1 1 := by
    have h := (hasDerivAt_pow 2 (1 : ℝ)).div_const 2
    simpa using h
  have b : HasDerivAt (fun t : ℝ => t ^ 4 / 2) (4 / 2) 1 := by
    have h := (hasDerivAt_pow 4 (1 : ℝ)).div_const 2
    simpa using h
  have hd := (a.add b).deriv
  rw [show (fun t : ℝ => t ^ 2 / 2 + t ^ 4 / 2) =
      (fun t : ℝ => t ^ 2 / 2) + (fun t : ℝ => t ^ 4 / 2) from by
    funext t
    simp [Pi.add_apply]]
  rw [hd]
  norm_num

#print axioms aug_gradient_eq_backward

end Cslib.MachineLearning.AugmentedAdjoint
