/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.KeyTheorems.Parameterized

open MetaMathlibExt.Complexity.KeyTheorems.Parameterized
open MetaMathlibExt.BitstringEncoding

-- The original target uses the machine-based reduction and the circuit definition of W[1].
example :
    (CliqueParam ∈ WLevel 1 ∧ ∀ P ∈ WLevel 1, FPTReduces P CliqueParam) ∧
    (∀ P : ParamProblem, FPT P → P ∈ WLevel 1) ∧
    ∀ t : ℕ, WLevel t ⊆ WLevel (t + 1) :=
  parameterized_clique_w1_complete

-- A subsequent Clique-to-Q reduction can now establish W[1]-hardness of Q.
example {Q : ParamProblem} (r : FPTReduces CliqueParam Q) :
    ∀ P ∈ WLevel 1, FPTReduces P Q :=
  fun P hP => (clique_wOne_hard P hP).trans r

-- The edgeless graph has a one-vertex clique even when the header dwarfs its edge list.
example : WeightedCircuitSat 1 3
    (CliqueMembership.reduce (bitEncode ((2 ^ 100 : ℕ), ([] : List (ℕ × ℕ))))) 1 := by
  apply (CliqueMembership.reduce_correct _ _).mp
  simp only [CliqueParam, bitDecode_bitEncode, decide_eq_true_eq]
  exact ⟨[0], by simp, rfl, by simp, by simp⟩
