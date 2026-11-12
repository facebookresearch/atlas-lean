/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.Ledger

@[expose] public section

/-!
# Finite sequences of balanced journal entries (Atlas AC01.T02)

`postAll b es` posts a finite list of journal entries, in order, to the ledger
balances `b`. If every entry is balanced, the initial trial-balance total is
preserved and so is the accounting equation. The proofs are list induction over the
single-step facts `sum_post_of_isBalanced` and `accountingEquation_post`.

## Main results

* `MathlibExt.Economics.Accounting.sum_postAll_of_forall_isBalanced`
* `MathlibExt.Economics.Accounting.accountingEquation_postAll`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §3.5
  (posting) and §3.6 (trial balance).
-/

namespace MathlibExt.Economics.Accounting

/-- Post a finite sequence of journal entries, in list order, to the ledger balances `b`. -/
def postAll {α : Type*} (b : α → ℝ) (es : List (α → ℝ)) : α → ℝ :=
  es.foldl post b

/-- Posting a finite sequence of balanced entries leaves the initial trial-balance total
unchanged. -/
theorem sum_postAll_of_forall_isBalanced {α : Type*} [Fintype α] {es : List (α → ℝ)}
    (hes : ∀ e ∈ es, IsBalanced e) (b : α → ℝ) :
    ∑ a, postAll b es a = ∑ a, b a := by
  induction es generalizing b with
  | nil =>
    simp [postAll, List.foldl_nil]
  | cons e es ih =>
    have he : IsBalanced e := hes e List.mem_cons_self
    have hrest : ∀ e' ∈ es, IsBalanced e' :=
      fun e' hm => hes e' (List.mem_cons_of_mem e hm)
    have hfold : postAll b (e :: es) = postAll (post b e) es := by
      unfold postAll
      exact List.foldl_cons
    rw [hfold, ih hrest (post b e)]
    exact sum_post_of_isBalanced he b

/-- Posting a finite sequence of balanced entries preserves the accounting equation. -/
theorem accountingEquation_postAll {α : Type*} [Fintype α] {cls : α → AccountClass}
    {b : α → ℝ} {es : List (α → ℝ)} (hb : AccountingEquation cls b)
    (hes : ∀ e ∈ es, IsBalanced e) :
    AccountingEquation cls (postAll b es) := by
  induction es generalizing b with
  | nil =>
    simpa [postAll, List.foldl_nil] using hb
  | cons e es ih =>
    have he : IsBalanced e := hes e List.mem_cons_self
    have hrest : ∀ e' ∈ es, IsBalanced e' :=
      fun e' hm => hes e' (List.mem_cons_of_mem e hm)
    have hstep : AccountingEquation cls (post b e) := accountingEquation_post hb he
    have hfold : postAll b (e :: es) = postAll (post b e) es := by
      unfold postAll
      exact List.foldl_cons
    rw [hfold]
    exact ih hstep hrest

end MathlibExt.Economics.Accounting
