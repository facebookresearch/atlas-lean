/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import MathlibExt.Analysis.Calculus.Gradient

/-!
# Backpropagation computes the gradient of a feedforward network

Backpropagation (Rumelhart, Hinton and Williams, *Learning representations by back-propagating
errors*, Nature 323, 1986; Bishop, *Pattern Recognition and Machine Learning*, Section 5.3) for
feedforward networks with arbitrary differentiable layers between Euclidean spaces of widths
`d 0, d 1, …`. The forward pass applies the layers in order. The backward pass starts from the
loss gradient at the output and applies the adjoint of each layer's Jacobian at its forward
activation, from the last layer to the first (Bishop's `δ` recursion).

Main results:

* The chain rule for gradients, `∇ (f ∘ g) x = (Dg x)† ∇ f (g x)`, is
  `MetaMathlibExt.gradient_comp` (`MathlibExt/Analysis/Calculus/Gradient.lean`).
* `Net.DiffAlong`: the traversed layers are differentiable at their forward activations (only
  these are assumed); `Net.diffAlong_of_differentiable`.
* `Net.backward_eq`: **the backward pass is the vector-Jacobian product** `(D forward_n x)† δ`.
* `gradient_comp_forward`: **backpropagation computes the input gradient** of `ℓ ∘ forward_n`.
* `gradient_param`: for networks with parameters (`PNet`), **backpropagation computes the
  gradient with respect to each layer's parameters**: the adjoint of the layer's parameter
  derivative applied to the vector backpropagated to the layer's output (`Net.shift`,
  `Net.forward_add`).

## Cost model

None: the subject is derivatives over the reals. As written, `backward` recomputes each forward
activation; caching the activations, as implementations do, does not change the values.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Backpropagation

open InnerProductSpace ContinuousLinearMap
open MetaMathlibExt (gradient_comp)
open scoped Gradient

/-- A feedforward network with layer widths `d`: layer `k` maps `ℝ^{d k}` to `ℝ^{d (k + 1)}`. -/
structure Net (d : ℕ → ℕ) where
  /-- The map computed by layer `k`. -/
  layer : (k : ℕ) → EuclideanSpace ℝ (Fin (d k)) → EuclideanSpace ℝ (Fin (d (k + 1)))

variable {d : ℕ → ℕ} (N : Net d)

/-- The forward pass through the first `n` layers. -/
def Net.forward : (n : ℕ) → EuclideanSpace ℝ (Fin (d 0)) → EuclideanSpace ℝ (Fin (d n))
  | 0, x => x
  | n + 1, x => N.layer n (forward n x)

/-- **The backward pass**: starting from a vector `δ` at the output of layer `n`, apply the
adjoint of each layer's Jacobian at its forward activation, from the last layer to the first. -/
noncomputable def Net.backward (x : EuclideanSpace ℝ (Fin (d 0))) :
    (n : ℕ) → EuclideanSpace ℝ (Fin (d n)) → EuclideanSpace ℝ (Fin (d 0))
  | 0, δ => δ
  | n + 1, δ => backward x n (adjoint (fderiv ℝ (N.layer n) (N.forward n x)) δ)

/-- The first `n` layers are differentiable at their forward activations from `x`. -/
def Net.DiffAlong (x : EuclideanSpace ℝ (Fin (d 0))) (n : ℕ) : Prop :=
  ∀ j < n, DifferentiableAt ℝ (N.layer j) (N.forward j x)

/-- Globally differentiable layers are differentiable along every forward pass. -/
theorem Net.diffAlong_of_differentiable (hN : ∀ k, Differentiable ℝ (N.layer k))
    (x : EuclideanSpace ℝ (Fin (d 0))) (n : ℕ) : N.DiffAlong x n :=
  fun j _ => (hN j).differentiableAt

/-- The forward pass is differentiable at `x` when the traversed layers are differentiable at
their activations. -/
theorem Net.differentiableAt_forward (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ n, N.DiffAlong x n → DifferentiableAt ℝ (N.forward n) x
  | 0, _ => differentiableAt_id
  | n + 1, hN => (hN n (by omega)).comp x
      (differentiableAt_forward x n fun j hj => hN j (by omega))

/-- **The backward pass is the vector-Jacobian product** of the forward pass: it applies the
adjoint of the network's derivative at the input. Only the `n` traversed layers need to be
differentiable, and only at their forward activations. -/
theorem Net.backward_eq (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ (n : ℕ), N.DiffAlong x n → ∀ δ : EuclideanSpace ℝ (Fin (d n)),
      N.backward x n δ = adjoint (fderiv ℝ (N.forward n) x) δ
  | 0, _, δ => by
      simp only [backward]
      rw [show N.forward 0 = id from rfl, fderiv_id, adjoint_id, id_apply]
  | n + 1, hN, δ => by
      have hN' : N.DiffAlong x n := fun j hj => hN j (by omega)
      have hcomp : N.forward (n + 1) = N.layer n ∘ N.forward n := rfl
      rw [backward, backward_eq x n hN', hcomp,
        fderiv_comp x (hN n (by omega)) (N.differentiableAt_forward x n hN'), adjoint_comp,
        comp_apply]

/-- **Backpropagation computes the input gradient**: for a differentiable loss `ℓ` on the output
of layer `n`, the gradient of `ℓ ∘ forward n` at `x` is the backward pass of the loss gradient. -/
theorem gradient_comp_forward {n : ℕ} (ℓ : EuclideanSpace ℝ (Fin (d n)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (d 0))) (hN : N.DiffAlong x n)
    (hℓ : DifferentiableAt ℝ ℓ (N.forward n x)) :
    ∇ (ℓ ∘ N.forward n) x = N.backward x n (∇ ℓ (N.forward n x)) := by
  rw [N.backward_eq x n hN, gradient_comp hℓ (N.differentiableAt_forward x n hN)]

/-! ## Parameter gradients -/

/-- The layers from `j` on, as a network of their own. -/
def Net.shift (j : ℕ) : Net (fun i => d (j + i)) := ⟨fun i => N.layer (j + i)⟩

/-- Running the first `j + m` layers is running the first `j`, then `m` more. -/
theorem Net.forward_add (j : ℕ) (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ m, N.forward (j + m) x = (N.shift j).forward m (N.forward j x)
  | 0 => rfl
  | m + 1 => by
      change N.layer (j + m) (N.forward (j + m) x) = _
      rw [forward_add j x m]
      rfl

/-- A network whose layers have parameters: layer `k` has parameters in `ℝ^{p k}`. -/
structure PNet (d p : ℕ → ℕ) where
  /-- The map computed by layer `k` with parameters `θ`. -/
  layer : (k : ℕ) → EuclideanSpace ℝ (Fin (p k)) → EuclideanSpace ℝ (Fin (d k)) →
    EuclideanSpace ℝ (Fin (d (k + 1)))

variable {p : ℕ → ℕ}

/-- The network with all parameters fixed. -/
def PNet.net (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k))) : Net d :=
  ⟨fun k => P.layer k (θ k)⟩

theorem PNet.forward_update_of_le (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k)))
    (k : ℕ) (t : EuclideanSpace ℝ (Fin (p k))) (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ j, j ≤ k → (P.net (Function.update θ k t)).forward j x = (P.net θ).forward j x
  | 0, _ => rfl
  | j + 1, hj => by
      change P.layer j (Function.update θ k t j) _ = P.layer j (θ j) _
      rw [Function.update_of_ne (by omega), forward_update_of_le P θ k t x j (by omega)]

theorem PNet.shift_update (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k))) (k : ℕ)
    (t : EuclideanSpace ℝ (Fin (p k))) :
    (P.net (Function.update θ k t)).shift (k + 1) = (P.net θ).shift (k + 1) := by
  simp only [Net.shift, PNet.net]
  congr 1
  funext i
  rw [Function.update_of_ne (by omega)]

/-- **Backpropagation computes the parameter gradients**: the gradient of the loss with respect
to the parameters of layer `k` is the adjoint of that layer's parameter derivative applied to the
vector backpropagated from the output to the layer's output. -/
theorem gradient_param (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k)))
    (x : EuclideanSpace ℝ (Fin (d 0))) (k m : ℕ)
    (hN : ∀ i < m, DifferentiableAt ℝ ((P.net θ).layer (k + 1 + i))
      ((P.net θ).forward (k + 1 + i) x))
    (hk : DifferentiableAt ℝ (fun t => P.layer k t ((P.net θ).forward k x)) (θ k))
    (ℓ : EuclideanSpace ℝ (Fin (d (k + 1 + m))) → ℝ)
    (hℓ : DifferentiableAt ℝ ℓ ((P.net θ).forward (k + 1 + m) x)) :
    ∇ (fun t => ℓ ((P.net (Function.update θ k t)).forward (k + 1 + m) x)) (θ k) =
      adjoint (fderiv ℝ (fun t => P.layer k t ((P.net θ).forward k x)) (θ k))
        (((P.net θ).shift (k + 1)).backward ((P.net θ).forward (k + 1) x) m
          (∇ ℓ ((P.net θ).forward (k + 1 + m) x))) := by
  set S := (P.net θ).shift (k + 1)
  set g := fun t => P.layer k t ((P.net θ).forward k x)
  have hfun : (fun t => ℓ ((P.net (Function.update θ k t)).forward (k + 1 + m) x)) =
      (ℓ ∘ S.forward m) ∘ g := by
    funext t
    rw [Net.forward_add, PNet.shift_update]
    change ℓ (S.forward m (P.layer k (Function.update θ k t k) _)) = _
    rw [Function.update_self, PNet.forward_update_of_le P θ k t x k le_rfl]
    rfl
  have hS : S.DiffAlong ((P.net θ).forward (k + 1) x) m := fun i hi => by
    change DifferentiableAt ℝ ((P.net θ).layer (k + 1 + i)) _
    rw [← Net.forward_add]
    exact hN i hi
  have hg : g (θ k) = (P.net θ).forward (k + 1) x := rfl
  have hout : S.forward m ((P.net θ).forward (k + 1) x) = (P.net θ).forward (k + 1 + m) x :=
    (Net.forward_add (P.net θ) (k + 1) x m).symm
  have hℓ' : DifferentiableAt ℝ ℓ (S.forward m ((P.net θ).forward (k + 1) x)) := by
    rw [hout]; exact hℓ
  rw [hfun, gradient_comp (f := ℓ ∘ S.forward m) (g := g)
      (by exact hℓ'.comp _ (S.differentiableAt_forward _ m hS)) hk, hg,
    gradient_comp_forward S ℓ _ hS hℓ', hout]

end Cslib.MachineLearning.Backpropagation
