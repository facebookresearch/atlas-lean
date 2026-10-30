/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Backpropagation

/-!
# Backpropagation tests

Closed checks: the theorems instantiated for a network of widths `2, 3, 4, …`. They cover a
three-layer input gradient with globally differentiable layers and a two-layer one assuming only
the traversed layers. They also cover the parameter gradient of layer `1` of a four-layer
parametrized network, assuming differentiability only of the layers after it. The definitions
involve derivatives over the reals and are not executable.
-/

namespace Cslib.MachineLearning.Backpropagation

open scoped Gradient

example (N : Net (fun k => k + 2)) (hN : ∀ k, Differentiable ℝ (N.layer k))
    (ℓ : EuclideanSpace ℝ (Fin (3 + 2)) → ℝ) (x : EuclideanSpace ℝ (Fin (0 + 2)))
    (hℓ : DifferentiableAt ℝ ℓ (N.forward 3 x)) :
    ∇ (ℓ ∘ N.forward 3) x = N.backward x 3 (∇ ℓ (N.forward 3 x)) :=
  gradient_comp_forward N ℓ x (N.diffAlong_of_differentiable hN x 3) hℓ

-- only the traversed layers matter: no assumption on layers `≥ 2`
example (N : Net (fun k => k + 2)) (x : EuclideanSpace ℝ (Fin (0 + 2))) (hN : N.DiffAlong x 2)
    (ℓ : EuclideanSpace ℝ (Fin (2 + 2)) → ℝ) (hℓ : DifferentiableAt ℝ ℓ (N.forward 2 x)) :
    ∇ (ℓ ∘ N.forward 2) x = N.backward x 2 (∇ ℓ (N.forward 2 x)) :=
  gradient_comp_forward N ℓ x hN hℓ

example (P : PNet (fun k => k + 2) (fun _ => 5)) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin 5))
    (x : EuclideanSpace ℝ (Fin (0 + 2)))
    (hN : ∀ i < 2, DifferentiableAt ℝ ((P.net θ).layer (1 + 1 + i))
      ((P.net θ).forward (1 + 1 + i) x))
    (hk : DifferentiableAt ℝ (fun t => P.layer 1 t ((P.net θ).forward 1 x)) (θ 1))
    (ℓ : EuclideanSpace ℝ (Fin (1 + 1 + 2 + 2)) → ℝ)
    (hℓ : DifferentiableAt ℝ ℓ ((P.net θ).forward (1 + 1 + 2) x)) :
    ∇ (fun t => ℓ ((P.net (Function.update θ 1 t)).forward (1 + 1 + 2) x)) (θ 1) =
      ContinuousLinearMap.adjoint (fderiv ℝ (fun t => P.layer 1 t ((P.net θ).forward 1 x)) (θ 1))
        (((P.net θ).shift (1 + 1)).backward ((P.net θ).forward (1 + 1) x) 2
          (∇ ℓ ((P.net θ).forward (1 + 1 + 2) x))) :=
  gradient_param P θ x 1 2 hN hk ℓ hℓ

#print axioms gradient_comp_forward
#print axioms gradient_param

end Cslib.MachineLearning.Backpropagation
