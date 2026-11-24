/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.FiniteSampleExpressivity
public import CSLibExt.MachineLearning.OneHiddenLayerNet
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-sample interpolation for one-hidden-layer ReLU networks

The general finite-sample expressivity theorem is supplied by the checked provider
`CSLibExt.MachineLearning.FiniteSampleExpressivity.exists_reluNet_eq` (following
Zhang, Bengio, Hardt, Recht and Vinyals, arXiv:1611.03530, Theorem 1 and
Appendix C, Lemma 1). The proof below is exactly that provider theorem: this file
only bridges the provider's sum form to the `Net` forward form via
`forward_oneHiddenLayerNet`, rewriting each bias term with
`sub_eq_add_neg`.
-/

@[expose] public section

namespace Cslib.MachineLearning.InterpolationExpressivity

open Cslib.MachineLearning.OneHiddenLayerNet

theorem exists_interpolating_net (n d : ℕ)
    (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Function.Injective z)
    (y : Fin n → ℝ) :
    ∃ (a : EuclideanSpace ℝ (Fin d)) (b w : Fin n → ℝ),
      ∀ i, (oneHiddenLayerNet d n (fun x => max x 0) (fun _ => a) (fun j => -b j) w).forward
        2 (z i) 0 = y i := by
  obtain ⟨a, b, w, h⟩ :=
    CSLibExt.MachineLearning.FiniteSampleExpressivity.exists_reluNet_eq hz y
  refine ⟨a, b, w, fun i => ?_⟩
  rw [forward_oneHiddenLayerNet, ← h i]
  simp only [CSLibExt.MachineLearning.FiniteSampleExpressivity.reluNet]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine congrArg (fun t => w j * t) ?_
  conv_rhs => rw [sub_eq_add_neg]

end Cslib.MachineLearning.InterpolationExpressivity
