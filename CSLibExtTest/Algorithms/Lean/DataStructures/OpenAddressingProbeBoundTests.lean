/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing.ProbeBound
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Cslib.Algorithms.Lean.OpenAddressingProbeBoundTests

open OpenAddressing

/-- Boundary check: with no occupied slots, no permutation has
its first probe occupied, so the count is `0 ≤ 2! * 0`. -/
example : ((Finset.univ.filter (fun π : Equiv.Perm (Fin 2) =>
      ∀ i : Fin 2, (i : ℕ) < 1 → π i ∈ (∅ : Finset (Fin 2)))).card : ℝ) ≤
    (Nat.factorial 2 : ℝ) * (((∅ : Finset (Fin 2)).card : ℝ) / 2) ^ 1 := by
  have h := first_k_probes_bound (∅ : Finset (Fin 2)) (by norm_num) 1
  simpa using h

end Cslib.Algorithms.Lean.OpenAddressingProbeBoundTests
