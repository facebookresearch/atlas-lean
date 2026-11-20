/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# National accounts: product = income = expenditure

GDP can be measured from production (gross output minus intermediate consumption), from the
incomes that production generates, and from final expenditure. This file proves that the three
measures agree for the input–output table of a closed economy whose rows and columns balance
(Atlas roadmap MA01.T01).

For a finite set of sectors, `intermediate i j` is the value of sector `i`'s output bought by
sector `j` as an intermediate input, `finalExpenditure i` is final expenditure (consumption,
investment, government purchases) on sector `i`'s output, `income j` is the income generated in
sector `j` (compensation of employees, operating surplus, net taxes on production), and
`grossOutput i` is the value of sector `i`'s output. The accounting identities are:

* sales (row) balance: `grossOutput i = ∑ j, intermediate i j + finalExpenditure i`, since each
  sector's output goes either to other sectors or to final users;
* cost (column) balance: `grossOutput j = ∑ i, intermediate i j + income j`, since the value of
  each sector's output pays for its intermediate inputs and the rest is income.

Under these identities, GDP by production `∑ j, (grossOutput j - ∑ i, intermediate i j)`, GDP by
income `∑ j, income j`, and GDP by expenditure `∑ i, finalExpenditure i` are equal
(`gdpProduction_eq_gdpIncome_eq_gdpExpenditure`). Income and final expenditure need not agree
sector by sector; only the totals agree, because intermediate sales cancel in the sum.

The file also records a bookkeeping fact about one shared per-transaction amount: grouping the
transactions by seller, by factor recipient, or by buyer gives the same total
(`totalBySeller_eq_totalByFactor_eq_totalByBuyer`). That is a regrouping of a single total, not
the national-accounts identity.

## Main results

* `MathlibExt.Economics.Accounting.NationalAccounts.gdpProduction_eq_gdpIncome_eq_gdpExpenditure`
* `MathlibExt.Economics.Accounting.NationalAccounts.totalBySeller_eq_totalByFactor_eq_totalByBuyer`

## References

* R. E. Miller, P. D. Blair, *Input-Output Analysis: Foundations and Extensions*, 2nd ed.,
  Cambridge University Press (2009), Chapter 2 (input–output transactions and the national
  accounts).
-/

@[expose] public section

namespace MathlibExt.Economics.Accounting.NationalAccounts

/-- The total of a per-transaction `amount`, grouped by seller. Every total classification
of the transactions gives the same total
(`totalBySeller_eq_totalByFactor_eq_totalByBuyer`). -/
noncomputable def totalBySeller {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (amount : ι → ℝ) (seller : ι → α) : ℝ :=
  ∑ p, ∑ t ∈ Finset.univ.filter (fun t => seller t = p), amount t

/-- The total of a per-transaction `amount`, grouped by factor-income recipient. -/
noncomputable def totalByFactor {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (amount : ι → ℝ) (factor : ι → γ) : ℝ :=
  ∑ k, ∑ t ∈ Finset.univ.filter (fun t => factor t = k), amount t

/-- The total of a per-transaction `amount`, grouped by buyer. -/
noncomputable def totalByBuyer {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (amount : ι → ℝ) (buyer : ι → β) : ℝ :=
  ∑ b, ∑ t ∈ Finset.univ.filter (fun t => buyer t = b), amount t

/-- A grouped sum over a total classification equals the ungrouped sum, since
the fibers partition `Finset.univ`. Private: it is a one-line specialization
of `Finset.sum_fiberwise_of_maps_to` used only by the regrouping identity. -/
private theorem grouped_sum_eq_ungrouped {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (amount : ι → ℝ) (g : ι → κ) :
    (∑ k, ∑ t ∈ Finset.univ.filter (fun t => g t = k), amount t) = ∑ t, amount t :=
  Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) amount

/-- **Regrouping one shared amount.** Grouping a single per-transaction `amount` by seller,
by factor recipient, or by buyer gives the same total, whatever the labels: each grouping
equals `∑ t, amount t`. Because one amount serves all three groupings, this is bookkeeping,
not the national-accounts identity; for that, with separate production, income, and
expenditure flows, see `gdpProduction_eq_gdpIncome_eq_gdpExpenditure`. -/
theorem totalBySeller_eq_totalByFactor_eq_totalByBuyer {ι α β γ : Type*} [Fintype ι]
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (amount : ι → ℝ) (seller : ι → α) (buyer : ι → β) (factor : ι → γ) :
    totalBySeller amount seller = totalByFactor amount factor ∧
      totalByFactor amount factor = totalByBuyer amount buyer := by
  have hp : totalBySeller amount seller = ∑ t, amount t :=
    grouped_sum_eq_ungrouped amount seller
  have hi : totalByFactor amount factor = ∑ t, amount t :=
    grouped_sum_eq_ungrouped amount factor
  have he : totalByBuyer amount buyer = ∑ t, amount t :=
    grouped_sum_eq_ungrouped amount buyer
  exact ⟨hp.trans hi.symm, hi.trans he.symm⟩

/-- GDP by the production approach: gross output minus intermediate consumption, summed
over sectors. `intermediate i j` is the value of sector `i`'s output bought by sector `j`
as an intermediate input, so sector `j`'s intermediate consumption is
`∑ i, intermediate i j`. -/
noncomputable def gdpProduction {ι : Type*} [Fintype ι] (grossOutput : ι → ℝ)
    (intermediate : ι → ι → ℝ) : ℝ :=
  ∑ j, (grossOutput j - ∑ i, intermediate i j)

/-- GDP by the income approach: the income generated in each sector (compensation of
employees, operating surplus, net taxes on production), summed over sectors. -/
noncomputable def gdpIncome {ι : Type*} [Fintype ι] (income : ι → ℝ) : ℝ :=
  ∑ j, income j

/-- GDP by the expenditure approach: final expenditure (consumption, investment, government
purchases) on each sector's output, summed over sectors. -/
noncomputable def gdpExpenditure {ι : Type*} [Fintype ι] (finalExpenditure : ι → ℝ) : ℝ :=
  ∑ i, finalExpenditure i

/-- **National-accounts triple identity** (Atlas roadmap MA01.T01). In a closed economy
whose input–output table balances by rows (`hsales`: each sector's gross output is sold to
other sectors or to final users) and by columns (`hcosts`: each sector's gross output pays
for its intermediate inputs, and the rest is income), GDP measured by production, by income,
and by expenditure is the same. The second equality is where the accounting matters:
intermediate sales appear in both balances and cancel in the totals. -/
theorem gdpProduction_eq_gdpIncome_eq_gdpExpenditure {ι : Type*} [Fintype ι]
    (grossOutput : ι → ℝ) (intermediate : ι → ι → ℝ) (income finalExpenditure : ι → ℝ)
    (hsales : ∀ i, grossOutput i = ∑ j, intermediate i j + finalExpenditure i)
    (hcosts : ∀ j, grossOutput j = ∑ i, intermediate i j + income j) :
    gdpProduction grossOutput intermediate = gdpIncome income ∧
      gdpIncome income = gdpExpenditure finalExpenditure := by
  have hinc : ∀ j, income j = grossOutput j - ∑ i, intermediate i j := fun j => by
    rw [hcosts j, add_sub_cancel_left]
  have hfin : ∀ i, finalExpenditure i = grossOutput i - ∑ j, intermediate i j := fun i => by
    rw [hsales i, add_sub_cancel_left]
  refine ⟨Finset.sum_congr rfl fun j _ => (hinc j).symm, ?_⟩
  simp only [gdpIncome, gdpExpenditure, hinc, hfin, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

end MathlibExt.Economics.Accounting.NationalAccounts
