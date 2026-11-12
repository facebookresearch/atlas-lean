/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.InventoryFlow
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.InventoryFlow

open MathlibExt.Economics.Accounting

/-- Test movements: two purchases, one sale, one shrinkage loss. -/
def kind4 : Fin 4 → InventoryFlow :=
  ![InventoryFlow.purchase, InventoryFlow.purchase, InventoryFlow.costOfSale,
    InventoryFlow.loss]

/-- Costs: purchases 50 and 30, cost of sale 60, loss 5. -/
def amount4 : Fin 4 → ℝ :=
  ![50, 30, 60, 5]

/-- Purchases 80, cost of goods sold 65, ending inventory 115 in the four-movement example. -/
theorem test_inventory4 :
    flowTotal kind4 InventoryFlow.purchase amount4 = 80 ∧
      costOfGoodsSold kind4 amount4 = 65 ∧ endingInventory 100 kind4 amount4 = 115 := by
  constructor
  · unfold flowTotal
    have h : Finset.univ.filter (fun i : Fin 4 => kind4 i = InventoryFlow.purchase) = {0, 1} := by
      decide
    rw [h]
    simp [amount4]
    norm_num
  · constructor
    · unfold costOfGoodsSold
      have h1 : flowTotal kind4 InventoryFlow.costOfSale amount4 = 60 := by
        unfold flowTotal
        have h : Finset.univ.filter (fun i : Fin 4 => kind4 i = InventoryFlow.costOfSale) = {2} := by
          decide
        rw [h]
        simp [amount4]
      have h2 : flowTotal kind4 InventoryFlow.loss amount4 = 5 := by
        unfold flowTotal
        have h : Finset.univ.filter (fun i : Fin 4 => kind4 i = InventoryFlow.loss) = {3} := by
          decide
        rw [h]
        simp [amount4]
      rw [h1, h2]
      norm_num
    · unfold endingInventory inventoryEffect
      simp [kind4, amount4, Fin.sum_univ_four]
      norm_num

/-- Leaving the loss out of cost of goods sold breaks the identity. -/
theorem test_loss_omitted_breaks :
    100 + flowTotal kind4 InventoryFlow.purchase amount4 ≠
      flowTotal kind4 InventoryFlow.costOfSale amount4 + endingInventory 100 kind4 amount4 := by
  have hP : flowTotal kind4 InventoryFlow.purchase amount4 = 80 := by
    unfold flowTotal
    have h : Finset.univ.filter (fun i : Fin 4 => kind4 i = InventoryFlow.purchase) = {0, 1} := by
      decide
    rw [h]
    simp [amount4]
    norm_num
  have hC : flowTotal kind4 InventoryFlow.costOfSale amount4 = 60 := by
    unfold flowTotal
    have h : Finset.univ.filter (fun i : Fin 4 => kind4 i = InventoryFlow.costOfSale) = {2} := by
      decide
    rw [h]
    simp [amount4]
  have hE : endingInventory 100 kind4 amount4 = 115 := by
    unfold endingInventory inventoryEffect
    simp [kind4, amount4, Fin.sum_univ_four]
    norm_num
  rw [hP, hC, hE]
  norm_num

/-- The inventory identity holds in the four-movement example, by `beginning_add_purchases`. -/
theorem test_identity_inventory4 :
    100 + flowTotal kind4 InventoryFlow.purchase amount4 =
      costOfGoodsSold kind4 amount4 + endingInventory 100 kind4 amount4 := by
  exact beginning_add_purchases 100 kind4 amount4

/-- For the four-movement classification, the identity holds for every amount and beginning inventory. -/
theorem test_identity_any_amounts (amount : Fin 4 → ℝ) (beginning : ℝ) :
    beginning + flowTotal kind4 InventoryFlow.purchase amount =
      costOfGoodsSold kind4 amount + endingInventory beginning kind4 amount := by
  exact beginning_add_purchases beginning kind4 amount

end MathlibExtTest.Economics.Accounting.InventoryFlow
