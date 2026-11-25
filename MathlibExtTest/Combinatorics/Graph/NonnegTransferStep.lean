/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Graph.NonnegTransferStep
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Nonnegative transfer-step checks

Concrete consumers of
`MathlibExt.Combinatorics.Graph.NonnegTransferStep`: a
two-node proportional transfer with retirement inside the
budget, and the same step outside the budget driving a stock
negative.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Budget-feasible and budget-violating steps

## iv. References

- `MathlibExt.Combinatorics.Graph.NonnegTransferStep`
-/

open Matrix

namespace MathlibExtTest.Combinatorics.Graph.NonnegTransferStep

open MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ## A. Budget-feasible and budget-violating steps -/

/-- Transfer fraction `1/2` of a stock of 10 from node 0 to
node 1, retirement rate `1/4` at node 0, source 1 at node 1:
updated stocks `![5/2, 10]` are nonnegative. -/
example : ∀ v, 0 ≤ (![5 / 2, 10] : Fin 2 → ℝ) v :=
  nonneg_transfer_step (![0] : Fin 1 → Fin 2) ![1]
    (m := ![10, 4]) (s := ![0, 1])
    (F := ![5]) (α := ![1 / 2])
    (r := ![5 / 2, 0]) (δ := ![1 / 4, 0])
    (by intro v; fin_cases v <;> norm_num)
    (by intro v; fin_cases v <;> norm_num)
    (by intro e; fin_cases e; norm_num)
    (by intro e; fin_cases e; norm_num)
    (by intro v; fin_cases v <;> norm_num)
    (by
      intro v
      fin_cases v <;>
        simp [Finset.sum_filter, Finset.sum_singleton] <;>
        norm_num)
    (by funext v; fin_cases v <;> simp [incidence_mulVec] <;> norm_num)

/-- Outside the budget (`α = 3/2`, sending 15 from a stock of
10), the same update rule drives node 0 negative, so the
budget hypothesis cannot be dropped. -/
example : (0 : ℝ) >
    (![10, 0] + (incidenceMatrix
        (![0] : Fin 1 → Fin 2) ![1]).mulVec ![15]
      + ![0, 0] - ![0, 0] : Fin 2 → ℝ) 0 := by
  simp only [Pi.add_apply, Pi.sub_apply, incidence_mulVec,
    Finset.sum_filter, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  norm_num

#print axioms
  MathlibExt.Combinatorics.Graph.ArcNetwork.nonneg_transfer_step

end MathlibExtTest.Combinatorics.Graph.NonnegTransferStep
