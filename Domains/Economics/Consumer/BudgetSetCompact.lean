/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Compactness of budget sets

With finitely many goods and strictly positive prices, the budget set of nonnegative bundles
whose cost does not exceed wealth is compact; with nonnegative wealth it is nonempty.

## i. Overview

Every affordable nonnegative bundle buys at most `w / p i` units of good `i`, so the budget set lies
in a compact box; it is closed as an intersection of closed half-spaces, hence compact
(`IsCompact.of_isClosed_subset`). Compactness does not need `0 ≤ w` (the set is empty otherwise).
With nonnegative wealth, a zero price makes the budget set unbounded, so not compact (see the
tests); with nonnegative prices and negative wealth the budget set is empty.

`nonnegBudgetSet p w` is the budget set with consumption set the nonnegative orthant. Other
budget-set definitions in ATLAS (with a general consumption set) are to be unified with it.

## ii. Main results

* `MathlibExt.Economics.Consumer.nonnegBudgetSet_subset_Icc`
* `MathlibExt.Economics.Consumer.isCompact_nonnegBudgetSet`
* `MathlibExt.Economics.Consumer.nonnegBudgetSet_nonempty`

## iii. References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory* (1995), §2.D and the proof of
  Proposition 3.C.1.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

/-- The budget set `{x | 0 ≤ x ∧ p ⬝ᵥ x ≤ w}`: bundles with nonnegative quantities of each of the
finitely many goods `ι` whose cost at prices `p` does not exceed wealth `w`. -/
def nonnegBudgetSet {ι : Type*} [Fintype ι] (p : ι → ℝ) (w : ℝ) : Set (ι → ℝ) :=
  {x | 0 ≤ x ∧ p ⬝ᵥ x ≤ w}

/-- Under strictly positive prices every affordable nonnegative bundle buys at most `w / p i`
units of good `i`. -/
theorem nonnegBudgetSet_subset_Icc {ι : Type*} [Fintype ι] {p : ι → ℝ} {w : ℝ}
    (hp : ∀ i, 0 < p i) : nonnegBudgetSet p w ⊆ Set.Icc 0 (fun i => w / p i) := by
  intro x hx
  obtain ⟨hx0, hcost⟩ := hx
  refine Set.mem_Icc.mpr ⟨hx0, fun i => ?_⟩
  have h1 : p i * x i ≤ p ⬝ᵥ x := by
    show p i * x i ≤ ∑ j, p j * x j
    exact Finset.single_le_sum (fun j _ => mul_nonneg (le_of_lt (hp j)) (hx0 j))
      (Finset.mem_univ i)
  have h2 : p i * x i ≤ w := le_trans h1 hcost
  show x i ≤ w / p i
  rw [le_div_iff₀ (hp i)]
  calc x i * p i = p i * x i := mul_comm _ _
    _ ≤ w := h2

/-- **Budget sets are compact** under strictly positive prices. -/
theorem isCompact_nonnegBudgetSet {ι : Type*} [Fintype ι] {p : ι → ℝ} {w : ℝ}
    (hp : ∀ i, 0 < p i) : IsCompact (nonnegBudgetSet p w) := by
  have hmul : ∀ i : ι, Continuous fun x : ι → ℝ => p i * x i :=
    fun i => continuous_const.mul (continuous_apply i)
  have hcont : Continuous fun x : ι → ℝ => p ⬝ᵥ x := by
    show Continuous fun x : ι → ℝ => ∑ i, p i * x i
    exact continuous_finsetSum _ fun i _ => hmul i
  have h1 : IsClosed {x : ι → ℝ | 0 ≤ x} := isClosed_le continuous_const continuous_id
  have h2 : IsClosed {x : ι → ℝ | p ⬝ᵥ x ≤ w} := isClosed_le hcont continuous_const
  have hclosed : IsClosed (nonnegBudgetSet p w) := h1.inter h2
  exact IsCompact.of_isClosed_subset isCompact_Icc hclosed (nonnegBudgetSet_subset_Icc hp)

/-- With nonnegative wealth the zero bundle is affordable, so the budget set is nonempty. -/
theorem nonnegBudgetSet_nonempty {ι : Type*} [Fintype ι] {p : ι → ℝ} {w : ℝ} (hw : 0 ≤ w) :
    (nonnegBudgetSet p w).Nonempty := by
  refine ⟨0, le_rfl, ?_⟩
  rw [dotProduct_zero]
  exact hw

end MathlibExt.Economics.Consumer
