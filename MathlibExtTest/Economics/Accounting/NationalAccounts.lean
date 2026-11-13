/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Accounting.NationalAccounts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.NationalAccounts

open MathlibExt.Economics.Accounting.NationalAccounts

/-- Three transactions, amounts `30, 40, 30`: grouped by seller, by factor recipient, or by
buyer, the total is `100`. Seller/buyer/factor triples are `(0, 1, 2)`, `(0, 0, 1)`,
`(1, 2, 0)`; the first and third transactions have seller, buyer, and factor pairwise
distinct. -/
example : totalBySeller (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![0, 0, 1] t : Fin 3)) = 100 ∧
    totalByFactor (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![2, 1, 0] t : Fin 3)) = 100 ∧
    totalByBuyer (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![1, 0, 2] t : Fin 3)) = 100 := by
  have htot : (∑ t : Fin 3, (![30, 40, 30] t : ℝ)) = 100 := by
    rw [Fin.sum_univ_three]
    norm_num
  have hp : totalBySeller (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![0, 0, 1] t : Fin 3)) = ∑ t : Fin 3, (![30, 40, 30] t : ℝ) := by
    unfold totalBySeller
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _
  have hi : totalByFactor (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![2, 1, 0] t : Fin 3)) = ∑ t : Fin 3, (![30, 40, 30] t : ℝ) := by
    unfold totalByFactor
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _
  have he : totalByBuyer (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![1, 0, 2] t : Fin 3)) = ∑ t : Fin 3, (![30, 40, 30] t : ℝ) := by
    unfold totalByBuyer
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _
  exact ⟨hp.trans htot, hi.trans htot, he.trans htot⟩

/-- A two-sector closed economy: intermediate sales `[[10, 20], [30, 5]]` (sector `i` sells
`intermediate i j` to sector `j`), final expenditure `(70, 15)`, gross output `(100, 50)`, and
income `(60, 25)`. Both balances hold, and GDP is `85` by production, income, and expenditure,
although sector `0`'s income (`60`) differs from final expenditure on its output (`70`). -/
example :
    gdpProduction (![100, 50] : Fin 2 → ℝ) ![![10, 20], ![30, 5]] = 85 ∧
      gdpIncome (![60, 25] : Fin 2 → ℝ) = 85 ∧
      gdpExpenditure (![70, 15] : Fin 2 → ℝ) = 85 ∧
      (![60, 25] : Fin 2 → ℝ) 0 ≠ (![70, 15] : Fin 2 → ℝ) 0 := by
  have h := gdpProduction_eq_gdpIncome_eq_gdpExpenditure (![100, 50] : Fin 2 → ℝ)
    ![![10, 20], ![30, 5]] ![60, 25] ![70, 15]
    (by norm_num [Fin.forall_fin_two, Fin.sum_univ_two])
    (by norm_num [Fin.forall_fin_two, Fin.sum_univ_two])
  have he : gdpExpenditure (![70, 15] : Fin 2 → ℝ) = 85 := by
    norm_num [gdpExpenditure, Fin.sum_univ_two]
  exact ⟨h.1.trans (h.2.trans he), h.2.trans he, he, by norm_num⟩

end MathlibExtTest.Economics.Accounting.NationalAccounts
