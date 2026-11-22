/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-!
# The inventory cost-flow identity (Atlas AC02.T03)

Each inventory movement (at cost) is a purchase, a cost of sale, or a loss adjustment.
Ending inventory of the perpetual record is beginning inventory plus purchases minus
sales and losses. With losses charged to cost of goods sold, beginning inventory plus
purchases equals cost of goods sold plus ending inventory.

## Main results

* `MathlibExt.Economics.Accounting.beginning_add_purchases`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §10.1 (goods
  available for sale; shrinkage reported in cost of goods sold).
-/

namespace MathlibExt.Economics.Accounting

/-- Classification of an inventory movement (at cost): a purchase, the cost of a sale, or
a loss adjustment (shrinkage, write-down). -/
inductive InventoryFlow
  | purchase
  | costOfSale
  | loss
  deriving DecidableEq

/-- Total cost of the movements of kind `k`. -/
def flowTotal {ι : Type*} [Fintype ι] (kind : ι → InventoryFlow) (k : InventoryFlow)
    (amount : ι → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => kind i = k), amount i

/-- Effect of movement `i` on the inventory account: purchases add their cost, sales and
losses remove it. -/
def inventoryEffect {ι : Type*} (kind : ι → InventoryFlow) (amount : ι → ℝ) (i : ι) : ℝ :=
  if kind i = InventoryFlow.purchase then amount i else -amount i

/-- Ending inventory of the perpetual record: beginning inventory plus the effect of every
movement of the period. -/
def endingInventory {ι : Type*} [Fintype ι] (beginning : ℝ) (kind : ι → InventoryFlow)
    (amount : ι → ℝ) : ℝ :=
  beginning + ∑ i, inventoryEffect kind amount i

/-- Cost of goods sold, under the convention that loss adjustments are charged to cost of
goods sold. -/
def costOfGoodsSold {ι : Type*} [Fintype ι] (kind : ι → InventoryFlow) (amount : ι → ℝ) :
    ℝ :=
  flowTotal kind InventoryFlow.costOfSale amount + flowTotal kind InventoryFlow.loss amount

/-- Within the non-purchase movements, the cost-of-sale filter is the global cost-of-sale filter. -/
private theorem ac02t03_filter_cost {ι : Type*} [Fintype ι] (kind : ι → InventoryFlow) :
    (Finset.univ.filter fun i => ¬kind i = InventoryFlow.purchase).filter
      (fun i => kind i = InventoryFlow.costOfSale) =
    Finset.univ.filter fun i => kind i = InventoryFlow.costOfSale := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact h.2
  · intro h
    constructor
    · intro hp
      rw [h] at hp
      exact absurd hp (by decide)
    · exact h

/-- Within the non-purchase movements, the non-cost-of-sale filter is the loss filter. -/
private theorem ac02t03_filter_loss {ι : Type*} [Fintype ι] (kind : ι → InventoryFlow) :
    (Finset.univ.filter fun i => ¬kind i = InventoryFlow.purchase).filter
      (fun i => ¬kind i = InventoryFlow.costOfSale) =
    Finset.univ.filter fun i => kind i = InventoryFlow.loss := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hnp, hnc⟩
    cases hki : kind i
    · exfalso
      exact hnp hki
    · exfalso
      exact hnc hki
    · rfl
  · intro h
    constructor
    · intro hp
      rw [h] at hp
      exact absurd hp (by decide)
    · intro hc
      rw [h] at hc
      exact absurd hc (by decide)

/-- Inventory identity: beginning inventory plus purchases equals cost of goods sold plus
ending inventory, when every movement is classified. -/
theorem beginning_add_purchases {ι : Type*} [Fintype ι] (beginning : ℝ)
    (kind : ι → InventoryFlow) (amount : ι → ℝ) :
    beginning + flowTotal kind InventoryFlow.purchase amount =
      costOfGoodsSold kind amount + endingInventory beginning kind amount := by
  unfold costOfGoodsSold endingInventory
  have hS : ∑ i, inventoryEffect kind amount i =
      flowTotal kind InventoryFlow.purchase amount -
      flowTotal kind InventoryFlow.costOfSale amount -
      flowTotal kind InventoryFlow.loss amount := by
    have hite := Finset.sum_ite (s := Finset.univ)
      (p := fun i => kind i = InventoryFlow.purchase) (f := amount) (g := fun i => -amount i)
    simp only [inventoryEffect, flowTotal] at hite ⊢
    have hneg := Finset.sum_neg_distrib
      (s := Finset.univ.filter fun i => ¬kind i = InventoryFlow.purchase) (f := amount)
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun i => ¬kind i = InventoryFlow.purchase)
      (fun i => kind i = InventoryFlow.costOfSale) amount
    rw [ac02t03_filter_cost, ac02t03_filter_loss] at hsplit
    linarith
  linarith [hS]

end MathlibExt.Economics.Accounting
