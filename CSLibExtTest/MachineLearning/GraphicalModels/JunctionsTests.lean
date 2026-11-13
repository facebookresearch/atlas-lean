/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.Junctions
public import Mathlib.Tactic.FinCases

/-!
# Tests for the canonical junctions

Exact marginals of the collider law and an instance of the chain statement with explicit tables.
-/

@[expose] public section

namespace Cslib.MachineLearning.JunctionsTests

open Cslib.MachineLearning GraphicalModels Junctions MetaMathlibExt.FiniteWeight

example : marginal berksonNet.joint {0, 2} ![true, true, true] = 1 / 2 := by
  have e : ({0, 2} : Set (Fin 3)) = {0} ∪ {2} := by
    ext v
    fin_cases v <;> decide
  rw [e]
  exact berkson_marginal_02

example : marginal berksonNet.joint {0, 1, 2} ![true, true, true] = 1 / 4 := by
  have e : ({0, 1, 2} : Set (Fin 3)) = {0} ∪ {1} ∪ {2} := by
    ext v
    fin_cases v <;> decide
  rw [e]
  exact berkson_marginal_012

example : CondIndep (BayesNet.mk chainPa (fun _ _ => fairCoin)).joint {0} {2} {1} :=
  condIndep_chain _

end Cslib.MachineLearning.JunctionsTests
