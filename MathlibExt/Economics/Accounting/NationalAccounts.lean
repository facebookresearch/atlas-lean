/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-!
# National accounts: product = income = expenditure

In a fully classified finite transaction system, aggregate product, aggregate
income, and aggregate expenditure are equal (Atlas roadmap MA01.T01). Each
transaction has exactly one producer, one buyer, and one income recipient, so
each classification partitions the transactions; `amount t` is the value
added / final value of transaction `t`, not gross intermediate sales, and
transfers are excluded.

## Main results

* `MathlibExt.Economics.Accounting.NationalAccounts.aggregateProduct`
* `MathlibExt.Economics.Accounting.NationalAccounts.aggregateIncome`
* `MathlibExt.Economics.Accounting.NationalAccounts.aggregateExpenditure`
* `MathlibExt.Economics.Accounting.NationalAccounts.product_eq_income_eq_expenditure`
-/

@[expose] public section

namespace MathlibExt.Economics.Accounting.NationalAccounts

/-- Aggregate product: sum over producers `p` of the value added of the
transactions they produce (source clause: "aggregate product"). `amount t` is
the VALUE ADDED / final value of transaction `t`, not gross intermediate sales;
transfers are excluded (they are not transactions in this system). -/
noncomputable def aggregateProduct {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (amount : ι → ℝ) (seller : ι → α) : ℝ :=
  ∑ p, ∑ t ∈ Finset.univ.filter (fun t => seller t = p), amount t

/-- Aggregate income: sum over factor recipients `k` of the value added of the
transactions whose income they receive (source clause: "aggregate income"). -/
noncomputable def aggregateIncome {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (amount : ι → ℝ) (factor : ι → γ) : ℝ :=
  ∑ k, ∑ t ∈ Finset.univ.filter (fun t => factor t = k), amount t

/-- Aggregate expenditure: sum over buyers `b` of the value added of the
transactions they purchase (source clause: "aggregate expenditure"). -/
noncomputable def aggregateExpenditure {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (amount : ι → ℝ) (buyer : ι → β) : ℝ :=
  ∑ b, ∑ t ∈ Finset.univ.filter (fun t => buyer t = b), amount t

/-- A grouped sum over a total classification equals the ungrouped sum, since
the fibers partition `Finset.univ`. Private: it is a one-line specialization
of `Finset.sum_fiberwise_of_maps_to` used only by the triple identity. -/
private theorem grouped_sum_eq_ungrouped {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (amount : ι → ℝ) (g : ι → κ) :
    (∑ k, ∑ t ∈ Finset.univ.filter (fun t => g t = k), amount t) = ∑ t, amount t :=
  Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) amount

/-- National-accounts triple identity (Atlas roadmap MA01.T01): in a fully
classified finite transaction system — every transaction has exactly one
producer, one buyer, and one income recipient, via total functions, so each
classification partitions the transactions — aggregate product, aggregate
income, and aggregate expenditure are equal. Gross/net, domestic/national,
and timing conventions are fixed uniformly for all three aggregates and are
not distinguished here. -/
theorem product_eq_income_eq_expenditure {ι α β γ : Type*} [Fintype ι] [Fintype α]
    [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (amount : ι → ℝ) (seller : ι → α) (buyer : ι → β) (factor : ι → γ) :
    aggregateProduct amount seller = aggregateIncome amount factor ∧
      aggregateIncome amount factor = aggregateExpenditure amount buyer := by
  have hp : aggregateProduct amount seller = ∑ t, amount t :=
    grouped_sum_eq_ungrouped amount seller
  have hi : aggregateIncome amount factor = ∑ t, amount t :=
    grouped_sum_eq_ungrouped amount factor
  have he : aggregateExpenditure amount buyer = ∑ t, amount t :=
    grouped_sum_eq_ungrouped amount buyer
  exact ⟨hp.trans hi.symm, hi.trans he.symm⟩

end MathlibExt.Economics.Accounting.NationalAccounts
