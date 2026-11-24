/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.SignNetworkGrowth
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Tests for sign-network growth bounds

A definitional check that a zero-layer network is a halfspace, a computed
parameter count on a closed architecture, Boolean-embedding coordinates on
a closed vector, closed numeric instances of the per-neuron and collapsed
bounds, and axiom audits for the public theorems of the production module.
-/

namespace Cslib.MachineLearning.PACLearning

example (d : ℕ) (w : ℕ → ℕ) : networkClass d w 0 = halfspaceClass d := rfl

-- With `d = 1`, `w = fun _ => 2`, `L = 1`: fan-ins `1` and `2`, widths
-- `2` and `1`, so `(1 + 1) * 2 + (2 + 1) * 1 = 4 + 3 = 7`.
example : paramCount 1 (fun _ => 2) 1 = 7 := by decide

def testVec : Fin 2 → Bool := fun i => decide (i = 0)

example : ((WithLp.equiv 2 (Fin 2 → ℝ)) (boolEmbed 2 testVec)) 0 = 1 := rfl

example : ((WithLp.equiv 2 (Fin 2 → ℝ)) (boolEmbed 2 testVec)) 1 = 0 := rfl

example : growthFunctionVec (neuronClass 2) 3 ≤
    growthFunctionVec (halfspaceClass 2) 3 :=
  growthFunctionVec_neuronClass_le 2 3

-- With `d = 1`, `w = fun _ => 1`, `L = 0`, `m = 2`: fan-in `1`, width
-- `1`, so `paramCount = (1 + 1) * 1 = 2` and the bound is `(e * 2) ^ 2`.
example : ((growthFunctionVec (networkClass 1 (fun _ => 1) 0) 2 : ℕ) : ℝ) ≤
    (Real.exp 1 * (2 : ℝ)) ^ 2 := by
  have hm : ∀ i, i ≤ 0 → fanIn 1 (fun _ => 1) i + 1 ≤ 2 := by
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    decide
  have h := growthFunctionVec_networkClass_le_exp_pow 1 (fun _ => 1) 0 2 hm
  have hpc : paramCount 1 (fun _ => 1) 0 = 2 := by decide
  rw [hpc] at h
  exact h

#print axioms growthFunctionVec_halfspaceClass_le_real
#print axioms growthFunctionVec_neuronAt_le_real
#print axioms growthFunctionVec_trunk_le
#print axioms growthFunctionVec_networkClass_le
#print axioms growthFunctionVec_networkClass_le_exp_pow

end Cslib.MachineLearning.PACLearning
