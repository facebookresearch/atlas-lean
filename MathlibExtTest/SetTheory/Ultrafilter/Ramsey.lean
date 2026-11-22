/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Ultrafilter.Ramsey
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Filter.Ultrafilter.Defs

@[expose] public section

open Set Function

namespace MathlibExtTest.SetTheory.Ultrafilter.Ramsey

open MetaMathlibExt

-- Logic 32: Ramsey ultrafilter

/-- Sanity check: for a nonprincipal `U` the hypotheses of `IsRamseyUltrafilter` are satisfiable,
so the definition is not vacuously true — the partition into pairs `{2n, 2n+1}` meets all
three and forces a genuine `X`. -/

theorem isRamsey_pairs (U : Ultrafilter ℕ) (hU : ∀ s : Set ℕ, s.Finite → s ∉ U)
    (h : IsRamseyUltrafilter U) : ∃ X ∈ U, ∀ n, (X ∩ {2 * n, 2 * n + 1}).Subsingleton := by
  refine h (fun n => {2 * n, 2 * n + 1}) ?_ ?_ ?_
  · intro m n hmn
    simp only [onFun, Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro a (rfl | rfl) <;> rintro (h | h) <;> omega
  · ext k
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨k / 2, by omega⟩
  · intro n
    exact hU _ (Set.toFinite _)

end MathlibExtTest.SetTheory.Ultrafilter.Ramsey

end
