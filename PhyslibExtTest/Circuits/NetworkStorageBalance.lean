/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Circuits.NetworkStorageBalance
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.NetworkStorageBalance

namespace PhyslibExtTest.Circuits.NetworkStorageBalance

/-- Tellegen at one node and one branch: `v = 5`, `iB = 3`, so both
sides are `15`, through the public lemma. -/
example : dotProduct (![5] : Fin 1 → ℝ) ![3]
    = dotProduct (![5] : Fin 1 → ℝ) ![3] :=
  branch_power_eq_node_power 1 1 !![1] ![5] ![3] ![5] ![3]
    (by ext i; fin_cases i; norm_num [Matrix.mulVec, dotProduct])
    (by ext i; fin_cases i; norm_num [Matrix.mulVec, dotProduct])

/-- Stored energy of one capacitor branch: `C = 2`, `v = 3` gives
`2 * 3^2 / 2 = 9`, and nonnegativity through the public lemma. -/
example : storedEnergy 1 {0} ∅ ![2] ![0] ![3] ![5] = 9 := by
  norm_num [storedEnergy, Finset.sum_singleton]

example : 0 ≤ storedEnergy 1 {0} ∅ ![2] ![0] ![3] ![5] :=
  storedEnergy_nonneg 1 {0} ∅ ![2] ![0] ![3] ![5]
    (by intro e _; fin_cases e; norm_num) (by intro e h; simp at h)

end PhyslibExtTest.Circuits.NetworkStorageBalance
