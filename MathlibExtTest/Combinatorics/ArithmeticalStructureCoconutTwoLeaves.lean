/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTwoLeaves

namespace MetaMathlibExt.ncard_arithmeticalStructure_coconutTree_two

-- A three-vertex path gives ballot weights 2, 2, and 1.
example :
    Set.ncard {x : (Fin 3 ⊕ Fin 2 → ℕ) × (Fin 3 ⊕ Fin 2 → ℕ) |
      IsArithmeticalStructure (coconutTree 3 2) x.1 x.2} =
      8 + 2 * Set.ncard {x : (Fin 1 ⊕ Fin 2 → ℕ) × (Fin 1 ⊕ Fin 2 → ℕ) |
        IsSmoothCoconut 1 2 x.1 x.2} +
      2 * Set.ncard {x : (Fin 2 ⊕ Fin 2 → ℕ) × (Fin 2 ⊕ Fin 2 → ℕ) |
        IsSmoothCoconut 2 2 x.1 x.2} +
      Set.ncard {x : (Fin 3 ⊕ Fin 2 → ℕ) × (Fin 3 ⊕ Fin 2 → ℕ) |
        IsSmoothCoconut 3 2 x.1 x.2} := by
  rw [ncard_arithmeticalStructure_coconutTree_two (by decide)]
  have hIcc : Finset.Icc 3 5 = ({3, 4, 5} : Finset ℕ) := by decide
  simp [hIcc, show ballotNumber 2 2 = 2 by decide, show ballotNumber 2 1 = 2 by decide,
    ballotNumber_zero_right, catalan_two, catalan_three, Nat.add_assoc]

end MetaMathlibExt.ncard_arithmeticalStructure_coconutTree_two
