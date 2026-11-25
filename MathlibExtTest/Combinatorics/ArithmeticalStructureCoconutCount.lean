/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ArithmeticalStructureCoconutCount

/-!
# Checks for the coconut tree counting formula

The examples exercise the ballot weights and the terms from deleting all or all but one leaf.
-/

namespace MetaMathlibExt.ncard_arithmeticalStructure_coconutTree

example : ballotNumber 3 2 = 5 := by decide

example : ballotNumber 3 4 = 0 := by decide

example : coconutCountTerm 1 0 = 1 := by simp [coconutCountTerm_zero]

example : coconutCountTerm 2 1 = 0 := by simp [coconutCountTerm]

example : coconutCountTerm 3 1 = 1 := by simp [coconutCountTerm, catalan_two]

-- A one-vertex path with two leaves has one structure in which both leaves have label one.
example : Set.ncard {x : (Fin 1 ⊕ Fin 2 → ℕ) × (Fin 1 ⊕ Fin 2 → ℕ) |
    IsArithmeticalStructure (coconutTree 1 2) x.1 x.2} =
    Set.ncard {x : (Fin 1 ⊕ Fin 2 → ℕ) × (Fin 1 ⊕ Fin 2 → ℕ) |
      IsSmoothCoconut 1 2 x.1 x.2} + 1 := by
  rw [ncard_arithmeticalStructure_coconutTree (by decide) (by decide)]
  simp [Finset.sum_range_succ, coconutCountTerm, ballotNumber]

-- For a two-vertex path, both lengths of smooth source contribute with weight one.
example : Set.ncard {x : (Fin 2 ⊕ Fin 2 → ℕ) × (Fin 2 ⊕ Fin 2 → ℕ) |
    IsArithmeticalStructure (coconutTree 2 2) x.1 x.2} =
    (∑ p ∈ ({1, 2} : Finset ℕ),
      Set.ncard {x : (Fin p ⊕ Fin 2 → ℕ) × (Fin p ⊕ Fin 2 → ℕ) |
        IsSmoothCoconut p 2 x.1 x.2}) + 3 := by
  rw [ncard_arithmeticalStructure_coconutTree (by decide) (by decide)]
  have hIcc : Finset.Icc 3 4 = ({3, 4} : Finset ℕ) := by decide
  simp [Finset.sum_range_succ, coconutCountTerm, ballotNumber, catalan_two, hIcc]

end MetaMathlibExt.ncard_arithmeticalStructure_coconutTree
