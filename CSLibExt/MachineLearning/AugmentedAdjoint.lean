/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-horizon adjoint via augmented-state backpropagation

For differentiable discrete dynamics `M_k`, stage losses `ell_k` and
initial cost `b`, lift `x0` to `(x0, b x0)`, apply augmented layers
`(x, a) ↦ (M_k x, a + ell_k x)`, and use the final readout
`(x, a) ↦ a + ell_N x`. The total cost is
`b(x0) + ∑_{k=0}^N ell_k(x_k)` with `x_{k+1} = M_k x_k`.

This file proves the resulting backward pass equals the input gradient
of the total cost, with one correction to the first pinned statement:
the backward pass through the layers must be followed by the lift
pullback, the initial-cost gradient `∇ b x`. Without it the statement
is false already at horizon `0` (where it would claim
`∇ (b + ellN) x = ∇ ellN x`); the test file carries that
counterexample. The corrected theorem is
`∇ J x = augBackward … + ∇ b x`.

## Scope

Uniform finite dimension `d` for all layers (a specialization of the
roadmap's varying-width statement). Differentiability is required only
at the forward activations, and at `x` for the lift. This is the input
gradient, not only the parameter gradient; no optimizer convergence or
continuous-adjoint / PDE limit is claimed. No inner-product structure
on the augmented product `EuclideanSpace × ℝ` is used: every adjoint
in the backward pass is on the physical space.

## Key results

- `augForward_fst`, `augForward_snd`: the augmented forward pass has
  physical component the trajectory and accumulator `b x` plus the
  stage losses along it.
- `aug_totalCost_eq`: the total cost is `b x` plus all stage losses
  plus the final loss.
- `aug_gradient_eq_backward`: the gradient of the total cost is the
  backward pass plus `∇ b x`.

## References

- `Cslib.MachineLearning.Backpropagation` (`gradient_comp_forward`),
  the non-augmented backpropagation theorem this generalizes.
-/

@[expose] public section

open InnerProductSpace
open scoped Gradient

namespace Cslib.MachineLearning.AugmentedAdjoint

/-- Augmented state: physical state plus a scalar loss accumulator. -/
abbrev AugState (d : ℕ) : Type :=
  EuclideanSpace ℝ (Fin d) × ℝ

/-- Lift an input `x` to the augmented state `(x, b x)`. -/
noncomputable def augLift {d : ℕ} (b : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : AugState d :=
  (x, b x)

/-- One augmented layer: `(x, a) ↦ (M x, a + ell x)`. -/
noncomputable def augLayer {d : ℕ} (M : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : EuclideanSpace ℝ (Fin d) → ℝ) (p : AugState d) : AugState d :=
  (M p.1, p.2 + ell p.1)

/-- Forward pass through the first `n` augmented layers. -/
noncomputable def augForward {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) : ℕ → AugState d → AugState d
  | 0 => id
  | n + 1 => augLayer (M n) (ell n) ∘ augForward M ell n

/-- Physical trajectory `x_0 = x`, `x_{k+1} = M_k x_k`. -/
noncomputable def augTraj {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x
  | n + 1 => M n (augTraj M x n)

/-- Final readout `(x, a) ↦ a + ellN x`. -/
noncomputable def augFinalLoss {d : ℕ} (ellN : EuclideanSpace ℝ (Fin d) → ℝ)
    (p : AugState d) : ℝ :=
  p.2 + ellN p.1

/-- One backward step through an augmented layer at activation `x`:
the cotangent `(δ, c)` to the output `(M x, a + ell x)` pulls back to
`(adjoint (D M x) δ + c • ∇ ell x, c)`. Only adjoints on the physical
space are used; the accumulator cotangent passes through unchanged. -/
noncomputable def augBackStep {d : ℕ}
    (M : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (δc : AugState d) : AugState d :=
  (ContinuousLinearMap.adjoint (fderiv ℝ M x) δc.1 + δc.2 • ∇ ell x, δc.2)

/-- Backward pass through the first `n` augmented layers, starting from
an output cotangent: apply the layer steps from the last layer to the
first. -/
noncomputable def augBack {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) :
    ℕ → EuclideanSpace ℝ (Fin d) → AugState d → AugState d
  | 0, _, δc => δc
  | n + 1, x, δc => augBack M ell n x
      (augBackStep (M n) (ell n) (augTraj M x n) δc)

/-- Backward pass for the total cost: start from the cotangent
`(∇ ellN (x_n), 1)` of the final readout and return its physical
component. -/
noncomputable def augBackward {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (ellN : EuclideanSpace ℝ (Fin d) → ℝ)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (augBack M ell n x (∇ ellN (augTraj M x n), 1)).1

/-- The physical component of the augmented forward pass is the trajectory. -/
theorem augForward_fst {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    (augForward M ell n (augLift b x)).1 = augTraj M x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [augForward, Function.comp_apply, augLayer, augTraj, ih]

/-- The accumulator of the augmented forward pass is `b x` plus the
stage losses along the trajectory. -/
theorem augForward_snd {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    (augForward M ell n (augLift b x)).2 =
      b x + ∑ k ∈ Finset.range n, ell k (augTraj M x k) := by
  induction n with
  | zero => simp [augForward, augLift]
  | succ n ih =>
      simp only [augForward, Function.comp_apply, augLayer, augForward_fst, ih,
        Finset.sum_range_succ]
      ring

/-- Total cost through the augmented pass equals `b x` plus all stage
losses plus the final loss. -/
theorem aug_totalCost_eq {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → ℝ) (ellN : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    augFinalLoss ellN (augForward M ell n (augLift b x)) =
      b x + (∑ k ∈ Finset.range n, ell k (augTraj M x k)) + ellN (augTraj M x n) := by
  simp only [augFinalLoss, augForward_fst, augForward_snd]

/-- Gradient of a sum. -/
theorem grad_add {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ∇ (fun y => f y + g y) x = ∇ f x + ∇ g x := by
  apply ext_inner_right ℝ
  intro v
  have hfg : fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    fderiv_add hf hg
  rw [inner_gradient_left, hfg, add_apply, inner_add_left, ← inner_gradient_left,
    ← inner_gradient_left]

/-- Gradient of a composition with a differentiable map, via the adjoint. -/
theorem grad_comp_adjoint {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d))
    (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x) :
    ∇ (fun z => g (f z)) x = (fderiv ℝ f x).adjoint (∇ g (f x)) := by
  apply ext_inner_right ℝ
  intro v
  have hcomp : fderiv ℝ (fun z => g (f z)) x
      = (fderiv ℝ g (f x)) ∘SL (fderiv ℝ f x) :=
    fderiv_comp x hg hf
  have hinner : (fderiv ℝ g (f x)) ((fderiv ℝ f x) v)
      = ⟪∇ g (f x), (fderiv ℝ f x) v⟫_ℝ :=
    inner_gradient_left.symm
  rw [inner_gradient_left, hcomp, ContinuousLinearMap.comp_apply, hinner,
    ContinuousLinearMap.adjoint_inner_left]

/-- Finite-horizon adjoint via augmented-state backpropagation (CORRECTED):
the gradient of the total cost at `x` is the backward pass (the `δ`
recursion through the augmented layers, starting from the cotangent
`(∇ ellN (x_n), 1)` of the final readout) PLUS the lift pullback, the
initial-cost gradient `∇ b x`. The lift `(x ↦ (x, b x))` contributes
`∇ b x` because the accumulator cotangent is `1`. No inner-product
structure on the augmented product is used. Differentiability is
required only at the forward activations (and at `x` for the lift). -/
theorem aug_gradient_eq_backward {d : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ell : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → ℝ) (ellN : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hM : ∀ k < n, DifferentiableAt ℝ (M k) (augTraj M x k))
    (hell : ∀ k < n, DifferentiableAt ℝ (ell k) (augTraj M x k))
    (hb : DifferentiableAt ℝ b x)
    (hellN : DifferentiableAt ℝ ellN (augTraj M x n)) :
    ∇ (fun y => augFinalLoss ellN (augForward M ell n (augLift b y))) x =
      augBackward M ell ellN n x + ∇ b x := by
  induction n generalizing ellN with
  | zero =>
      have hJ : (fun y => augFinalLoss ellN (augForward M ell 0 (augLift b y)))
          = (fun y => b y + ellN y) := rfl
      have hB : augBackward M ell ellN 0 x = ∇ ellN x := rfl
      have hellN0 : DifferentiableAt ℝ ellN x := hellN
      have hAdd := grad_add b ellN x hb hellN0
      rw [hJ, hB, hAdd, add_comm]
  | succ n ih =>
      have hMn : DifferentiableAt ℝ (M n) (augTraj M x n) := hM n (by omega)
      have helln : DifferentiableAt ℝ (ell n) (augTraj M x n) := hell n (by omega)
      have hM' : ∀ k < n, DifferentiableAt ℝ (M k) (augTraj M x k) :=
        fun k hk => hM k (by omega)
      have hell' : ∀ k < n, DifferentiableAt ℝ (ell k) (augTraj M x k) :=
        fun k hk => hell k (by omega)
      have htraj : augTraj M x (n + 1) = M n (augTraj M x n) := rfl
      have hellN_at : DifferentiableAt ℝ ellN (M n (augTraj M x n)) := hellN
      have hcomp : DifferentiableAt ℝ (fun z => ellN (M n z)) (augTraj M x n) :=
        hellN_at.comp (augTraj M x n) hMn
      have hellN' : DifferentiableAt ℝ (fun z => ell n z + ellN (M n z))
          (augTraj M x n) :=
        helln.add hcomp
      have ih' := ih (fun z => ell n z + ellN (M n z)) hM' hell' hellN'
      have hfun : (fun y => augFinalLoss ellN (augForward M ell (n + 1) (augLift b y)))
          = (fun y => augFinalLoss (fun z => ell n z + ellN (M n z))
              (augForward M ell n (augLift b y))) := by
        funext y
        simp only [augForward, Function.comp_apply, augLayer, augFinalLoss]
        ring
      rw [hfun, ih']
      congr 1
      have h1 := grad_add (ell n) (fun z => ellN (M n z)) (augTraj M x n)
        helln hcomp
      have h2 := grad_comp_adjoint ellN (M n) (augTraj M x n) hellN_at hMn
      rw [h2] at h1
      have hgrad : ∇ (fun z => ell n z + ellN (M n z)) (augTraj M x n)
          = ∇ (ell n) (augTraj M x n)
            + (fderiv ℝ (M n) (augTraj M x n)).adjoint
              (∇ ellN (M n (augTraj M x n))) := h1
      have hcot : (∇ (fun z => ell n z + ellN (M n z)) (augTraj M x n), 1)
          = augBackStep (M n) (ell n) (augTraj M x n)
            (∇ ellN (augTraj M x (n + 1)), 1) := by
        simp only [augBackStep]
        rw [hgrad, htraj]
        congr 1
        rw [one_smul, add_comm]
      simp only [augBackward, augBack, hcot]

end Cslib.MachineLearning.AugmentedAdjoint
