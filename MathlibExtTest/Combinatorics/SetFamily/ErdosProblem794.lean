/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.ErdosProblem794
import Mathlib.Data.Fintype.Powerset

open MathlibExt.Combinatorics.ErdosProblem794Wanted

example : sixVertexFamily.card = 10 := by decide

example : ∀ S : Finset (Fin 6), S.card = 4 →
    (sixVertexFamily.filter fun e => e ⊆ S).card = 2 := by decide

example : ∀ S : Finset (Fin 6), S.card = 5 →
    (sixVertexFamily.filter fun e => e ⊆ S).card = 5 := by decide

-- Deleting one triple gives a counterexample exactly at the conjectured threshold.
example :
    let H := sixVertexFamily.erase {0, 1, 2}
    H.card = 2 ^ 3 + 1 ∧ SetFamily.IsUniform H 3 ∧
      ¬ (SetFamily.ContainsSubgraph H 4 3 ∨ SetFamily.ContainsSubgraph H 5 7) := by
  unfold SetFamily.IsUniform SetFamily.ContainsSubgraph
  decide
