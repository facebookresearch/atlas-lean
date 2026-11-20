/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Urban.StockBalance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Urban stock-balance checks

Concrete consumers of `MathlibExt.Urban.StockBalance`:
relocation between two compartments keeping the total, and a
two-period total with additions and an explicit retirement,
in one stock unit (asset counts).

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Relocation and retirement

## iv. References

- `MathlibExt.Urban.StockBalance`
-/

open Matrix
open Urban
open MathlibExt.Combinatorics.Graph.ArcNetwork

namespace MathlibExtTest.Urban.StockBalance

/-! ## A. Relocation and retirement -/

/-- Moving 2 assets from compartment 0 to compartment 1
keeps the total of 9. -/
example : ∑ v, (![3, 6] : Fin 2 → ℝ) v
    = ∑ v, (![5, 4] : Fin 2 → ℝ) v :=
  urbanStock_total_eq_of_no_external
    (![0] : Fin 1 → Fin 2) ![1] ![2]
    (m := ![5, 4])
    (by funext v; fin_cases v <;> simp [incidence_mulVec] <;> norm_num)

/-- Two periods: additions 1 then 2, retirements 0 then 4
move the total from 9 to 8. -/
example : True := by
  have h := urbanStock_total_multiperiod
    (![0] : Fin 1 → Fin 2) ![1] (fun _ => ![0])
    (m := fun t => if t = 0 then ![9, 0]
      else if t = 1 then ![10, 0] else ![8, 0])
    (s := fun t => if t = 0 then ![1, 0] else ![2, 0])
    (r := fun t => if t = 0 then ![0, 0] else ![4, 0]) 2
    (by
      intro t ht
      interval_cases t <;> funext v <;> fin_cases v <;>
        simp [incidence_mulVec] <;> norm_num)
  have htot : (∑ v, (![8, 0] : Fin 2 → ℝ) v)
      = (∑ v, (![9, 0] : Fin 2 → ℝ) v) + (1 + 2) - (0 + 4) := by
    convert h using 2 <;> simp [Finset.sum_range_succ, Fin.sum_univ_two]
  norm_num [Fin.sum_univ_two] at htot
  trivial

#print axioms Urban.urbanStock_total_eq_of_no_external
#print axioms Urban.urbanStock_total_multiperiod

end MathlibExtTest.Urban.StockBalance
