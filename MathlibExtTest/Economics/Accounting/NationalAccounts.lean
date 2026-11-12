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

/-- Three transactions, amounts `30, 40, 30`: product = income = expenditure = `100`.
Seller/buyer/factor triples are `(0, 1, 2)`, `(0, 0, 1)`, `(1, 2, 0)`; the first
and third transactions have seller, buyer, and factor pairwise distinct. -/
example : aggregateProduct (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![0, 0, 1] t : Fin 3)) = 100 ∧
    aggregateIncome (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![2, 1, 0] t : Fin 3)) = 100 ∧
    aggregateExpenditure (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![1, 0, 2] t : Fin 3)) = 100 := by
  have htot : (∑ t : Fin 3, (![30, 40, 30] t : ℝ)) = 100 := by
    rw [Fin.sum_univ_three]
    norm_num
  have hp : aggregateProduct (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![0, 0, 1] t : Fin 3)) = ∑ t : Fin 3, (![30, 40, 30] t : ℝ) := by
    unfold aggregateProduct
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _
  have hi : aggregateIncome (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![2, 1, 0] t : Fin 3)) = ∑ t : Fin 3, (![30, 40, 30] t : ℝ) := by
    unfold aggregateIncome
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _
  have he : aggregateExpenditure (fun t : Fin 3 => (![30, 40, 30] t : ℝ))
      (fun t : Fin 3 => (![1, 0, 2] t : Fin 3)) = ∑ t : Fin 3, (![30, 40, 30] t : ℝ) := by
    unfold aggregateExpenditure
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _
  exact ⟨hp.trans htot, hi.trans htot, he.trans htot⟩

end MathlibExtTest.Economics.Accounting.NationalAccounts
