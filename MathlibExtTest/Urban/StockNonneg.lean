/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Urban.StockNonneg
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Urban stock nonnegativity checks

Concrete consumers of `MathlibExt.Urban.StockNonneg` on
two-zone accounts: new construction into a zero-stock zone,
a retirement overdraw and a negative transfer (both
rejected by the hypotheses and genuinely negative after
the update), a loop transfer, parallel transfers, and the
no-transfer update.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Certificate consumers
- B. Necessity controls

## iv. References

- `MathlibExt.Urban.StockNonneg`
-/

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork
open Urban

namespace MathlibExtTest.Urban.StockNonneg

/-! ## A. Certificate consumers -/

/-- New construction into a zero-stock zone: stocks
`(10, 0)`, transfer `4` from zone `0` to zone `1`,
additions `(1, 2)`, retirements `(3, 0)` give `(4, 6)`. -/
example : (∀ v : Fin 2, 0 ≤ ((![10, 0] + (incidenceMatrix
      (![0] : Fin 1 → Fin 2) ![1]).mulVec ![4] + ![1, 2] - ![3, 0] :
      Fin 2 → ℝ)) v) ∧
    (![10, 0] + (incidenceMatrix (![0] : Fin 1 → Fin 2) ![1]).mulVec ![4]
      + ![1, 2] - ![3, 0] : Fin 2 → ℝ) = ![4, 6] := by
  have hcert := urbanStock_nonneg_of_outgoing_le (![0] : Fin 1 → Fin 2) ![1]
    (F := ![4]) (m := ![10, 0])
    (m' := ![10, 0] + (incidenceMatrix (![0] : Fin 1 → Fin 2) ![1]).mulVec ![4]
      + ![1, 2] - ![3, 0])
    (s := ![1, 2]) (r := ![3, 0])
    (fun v => by fin_cases v <;> norm_num)
    (fun v => by fin_cases v <;> norm_num)
    (fun e => by fin_cases e <;> norm_num)
    (fun v => by fin_cases v <;> norm_num)
    (fun v => by
      fin_cases v <;>
        norm_num [Finset.sum_filter, Fin.sum_univ_one, Matrix.cons_val_zero])
    rfl
  refine ⟨hcert, ?_⟩
  funext v
  fin_cases v <;>
    simp [Matrix.mulVec, dotProduct, incidenceMatrix,
      Pi.add_apply, Pi.sub_apply] <;> norm_num

/-- A loop transfer moves nothing between zones. -/
example : (![10, 3] + (incidenceMatrix (![0] : Fin 1 → Fin 2)
      ![0]).mulVec ![5] + ![0, 0] - ![0, 0] : Fin 2 → ℝ) = ![10, 3] := by
  funext v
  fin_cases v <;>
    simp [Matrix.mulVec, dotProduct, incidenceMatrix,
      Pi.add_apply, Pi.sub_apply]

/-- Parallel transfers `2` and `3` from zone `0` to zone
`1`: `(10, 0)` becomes `(5, 5)`, nonnegative by the
certificate. -/
example : (∀ v : Fin 2, 0 ≤ ((![10, 0] + (incidenceMatrix
      (![0, 0] : Fin 2 → Fin 2) ![1, 1]).mulVec ![2, 3] + ![0, 0] - ![0, 0] :
      Fin 2 → ℝ)) v) ∧
    (![10, 0] + (incidenceMatrix (![0, 0] : Fin 2 → Fin 2) ![1, 1]).mulVec
      ![2, 3] + ![0, 0] - ![0, 0] : Fin 2 → ℝ) = ![5, 5] := by
  have hcert := urbanStock_nonneg_of_outgoing_le (![0, 0] : Fin 2 → Fin 2)
    ![1, 1] (F := ![2, 3]) (m := ![10, 0])
    (m' := ![10, 0] + (incidenceMatrix (![0, 0] : Fin 2 → Fin 2)
      ![1, 1]).mulVec ![2, 3] + ![0, 0] - ![0, 0])
    (s := ![0, 0]) (r := ![0, 0])
    (fun v => by fin_cases v <;> norm_num)
    (fun v => by fin_cases v <;> norm_num)
    (fun e => by fin_cases e <;> norm_num)
    (fun v => by fin_cases v <;> norm_num)
    (fun v => by
      fin_cases v <;>
        norm_num [Finset.sum_filter, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one])
    rfl
  refine ⟨hcert, ?_⟩
  funext v
  fin_cases v <;>
    simp [Matrix.mulVec, dotProduct, incidenceMatrix, Fin.sum_univ_two,
      Pi.add_apply, Pi.sub_apply] <;> norm_num

/-- No transfers: additions and retirements only,
`(5, 7)` becomes `(4, 0)`. -/
example : ∀ v : Fin 2, 0 ≤ ((![5, 7] + (incidenceMatrix
      (Fin.elim0 : Fin 0 → Fin 2) Fin.elim0).mulVec (fun e => e.elim0)
      + ![1, 0] - ![2, 7] : Fin 2 → ℝ)) v := by
  apply urbanStock_nonneg_of_outgoing_le (Fin.elim0 : Fin 0 → Fin 2) Fin.elim0
    (F := fun e => e.elim0) (m := ![5, 7]) (s := ![1, 0]) (r := ![2, 7])
  · intro v
    fin_cases v <;> norm_num
  · intro v
    fin_cases v <;> norm_num
  · intro e
    exact e.elim0
  · intro v
    fin_cases v <;> norm_num
  · intro v
    fin_cases v <;> norm_num [Finset.sum_filter]
  · rfl

/-! ## B. Necessity controls -/

/-- Retirement overdraw is rejected: retiring `7` from a
stock of `5` violates the outgoing bound and drives the
updated stock negative. -/
example : ¬ ((∑ e ∈ (Finset.univ : Finset (Fin 0)).filter
      (fun e => (Fin.elim0 : Fin 0 → Fin 1) e = 0), (fun e => e.elim0) e)
    + ![7] 0 ≤ ![5] 0) ∧
    ¬ 0 ≤ (![5] + (incidenceMatrix (Fin.elim0 : Fin 0 → Fin 1)
      Fin.elim0).mulVec (fun e => e.elim0) + ![0] - ![7] : Fin 1 → ℝ) 0 := by
  constructor <;> norm_num [Matrix.mulVec, dotProduct]

/-- Negative transfer is rejected: `F = -20` fails the
amount hypothesis and drives the receiving zone negative. -/
example : ¬ (0 : ℝ) ≤ (![-20] : Fin 1 → ℝ) 0 ∧
    ¬ 0 ≤ (![10, 10] + (incidenceMatrix (![0] : Fin 1 → Fin 2)
      ![1]).mulVec ![-20] + ![0, 0] - ![0, 0] : Fin 2 → ℝ) 1 := by
  constructor
  · norm_num
  · norm_num [Matrix.mulVec, dotProduct, incidenceMatrix, Fin.sum_univ_one,
      Pi.add_apply, Pi.sub_apply]

#print axioms Urban.urbanStock_nonneg_of_outgoing_le

end MathlibExtTest.Urban.StockNonneg
