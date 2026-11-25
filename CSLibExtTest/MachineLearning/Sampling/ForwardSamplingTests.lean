/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.ForwardSampling
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Tests for forward sampling and rejection conditioning

A two-node Boolean network checks the forward-sampling law, an evidence
probability, and the resulting posterior mass.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.ForwardSamplingTests

open Finset Convexity Cslib.MachineLearning.GraphicalModels
open scoped ENNReal

/-- The distribution on `Bool` with `P(true) = p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

@[simp]
theorem coin_weights (p : ℝ) (h0 h1) (v : Bool) :
    (coin p h0 h1).weights v = if v then p else 1 - p := by
  cases v <;> simp [coin, StdSimplex.duple]

/-- A two-node network: `X₀` is fair, and `P(X₁ = true | X₀) = 3 / 4` if
`X₀ = true`, else `1 / 4`. Every node may read every earlier node. -/
noncomputable def twoNode : BayesNet Bool 2 where
  pa _ := univ
  cpt k u := if h0 : (k : ℕ) = 0 then coin (1 / 2) (by norm_num) (by norm_num)
    else if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (3 / 4) (by norm_num) (by norm_num)
      else coin (1 / 4) (by norm_num) (by norm_num)

theorem twoNode_joint_true_true : twoNode.joint ![true, true] = 3 / 8 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_two]
  simp [twoNode, coin_weights]
  norm_num

theorem twoNode_joint_false_true : twoNode.joint ![false, true] = 1 / 8 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_two]
  simp [twoNode, coin_weights]
  norm_num

theorem twoNode_sample_true_true :
    twoNode.samplePMF ![true, true] = ENNReal.ofReal (3 / 8) := by
  rw [BayesNet.samplePMF_apply, twoNode_joint_true_true]

theorem twoNode_evidenceProb_second_true :
    twoNode.evidenceProb {1} ![true, true] = 1 / 2 := by
  unfold BayesNet.evidenceProb
  have hset : (Finset.univ.filter fun x : Fin 2 → Bool => ∀ k ∈ ({1} : Finset (Fin 2)),
      x k = ![true, true] k) = {![true, true], ![false, true]} := by decide
  rw [hset, Finset.sum_pair (by decide)]
  rw [twoNode_joint_true_true, twoNode_joint_false_true]
  norm_num

theorem twoNode_posterior_true_true
    (hE : twoNode.evidenceProb {1} ![true, true] ≠ 0) :
    twoNode.posteriorPMF {1} ![true, true] hE ![true, true] =
      ENNReal.ofReal (3 / 4) := by
  rw [BayesNet.posteriorPMF_apply, ite_eq_left (fun k _ => rfl),
    twoNode_joint_true_true, twoNode_evidenceProb_second_true]
  congr 1
  norm_num

end Cslib.MachineLearning.ForwardSamplingTests
