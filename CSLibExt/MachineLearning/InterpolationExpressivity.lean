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
`forward_oneHiddenLayerNet` and the termwise identification of the positive part
with the displayed maximum.
-/

@[expose] public section

namespace Cslib.MachineLearning.InterpolationExpressivity

open Cslib.MachineLearning.OneHiddenLayerNet

theorem exists_interpolating_net (n d : ℕ)
    (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Function.Injective z)
    (y : Fin n → ℝ) :
    ∃ (a : EuclideanSpace ℝ (Fin d)) (b w : Fin n → ℝ),
      ∀ i, (oneHiddenLayerNet d n (fun x => x⁺) (fun _ => a) (fun j => -b j) w).forward
        2 (z i) 0 = y i := by
  obtain ⟨a, b, w, h⟩ :=
    CSLibExt.MachineLearning.FiniteSampleExpressivity.exists_reluNet_eq hz y
  refine ⟨a, b, w, fun i => ?_⟩
  have hmax : ∀ t : ℝ, t⁺ = max t 0 := fun t =>
    (posPart_def t).trans (le_antisymm (sup_le (le_max_left _ _) (le_max_right _ _))
      (max_le le_sup_left le_sup_right))
  rw [forward_oneHiddenLayerNet, ← h i]
  simp only [CSLibExt.MachineLearning.FiniteSampleExpressivity.reluNet]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine congrArg (fun t => w j * t) ?_
  conv_rhs => rw [sub_eq_add_neg]
  exact hmax _

end Cslib.MachineLearning.InterpolationExpressivity
