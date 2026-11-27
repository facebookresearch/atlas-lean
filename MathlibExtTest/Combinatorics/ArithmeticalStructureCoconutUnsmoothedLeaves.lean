/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ArithmeticalStructureCoconutUnsmoothedLeaves

open MetaMathlibExt

-- On a star the path has no noncentral vertices, so the sole term has weight one.
example (s : ℕ) (hs : 2 ≤ s) :
    Set.ncard {x : (Fin 1 ⊕ Fin s → ℕ) × (Fin 1 ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree 1 s) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)} =
    Set.ncard {z : (Fin 1 ⊕ Fin s → ℕ) × (Fin 1 ⊕ Fin s → ℕ) | IsSmoothCoconut 1 s z.1 z.2} := by
  simpa [ballotNumber_zero_right] using
    ncard_arithmeticalStructure_coconutTree_leaves_ge_two (p := 1) le_rfl hs

-- For two path vertices the interval contains both possible smooth path sizes.
example :
    Set.ncard {x : (Fin 2 ⊕ Fin 2 → ℕ) × (Fin 2 ⊕ Fin 2 → ℕ) |
      IsArithmeticalStructure (coconutTree 2 2) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)} =
    Set.ncard {x : (Fin 1 ⊕ Fin 2 → ℕ) × (Fin 1 ⊕ Fin 2 → ℕ) |
      IsSmoothCoconut 1 2 x.1 x.2} +
    Set.ncard {x : (Fin 2 ⊕ Fin 2 → ℕ) × (Fin 2 ⊕ Fin 2 → ℕ) |
      IsSmoothCoconut 2 2 x.1 x.2} := by
  simpa [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide, ballotNumber] using
    ncard_arithmeticalStructure_coconutTree_leaves_ge_two (p := 2) (s := 2) (by decide) le_rfl
