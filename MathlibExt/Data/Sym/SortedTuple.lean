/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Sort

/-!
# Original symmetric powers as actual monotone tuples

Native multiset sorting and the original `List.ofFn` give inverse maps
between symmetric powers and monotone finite tuples. Native stars and bars
therefore counts the actual monotone tuples, without supplying a counting
or sorting certificate.
-/

@[expose] public section
noncomputable section

namespace Sym

variable {α : Type*} [LinearOrder α]

/-- Native sorting is the equivalence from the original symmetric power to monotone tuples. -/
def sortedTupleEquiv (n : ℕ) : Sym α n ≃ {f : Fin n → α // Monotone f} where
  toFun s := by
    let l := s.val.sort (· ≤ ·)
    have hl : l.length = n := by simpa only [l, Multiset.length_sort] using s.property
    exact ⟨fun i => l.get (Fin.cast hl.symm i), fun _ _ h =>
      (Multiset.pairwise_sort s.val (· ≤ ·)).rel_get_of_le h⟩
  invFun f := ⟨↑(List.ofFn f.val), by simp⟩
  left_inv s := by
    apply Subtype.ext
    change (↑(List.ofFn (fun i : Fin n =>
      (s.val.sort (· ≤ ·)).get (Fin.cast (by simp only [Multiset.length_sort, s.property]) i))) :
        Multiset α) = s.val
    rw [← List.ofFn_congr (by simp only [Multiset.length_sort, s.property])
      (s.val.sort (· ≤ ·)).get, List.ofFn_get, Multiset.sort_eq]
  right_inv f := by
    apply Subtype.ext
    apply List.ofFn_injective
    have hsorted : (List.ofFn f.val).Pairwise (· ≤ ·) := f.property.sortedLE_ofFn.pairwise
    have hsort : (↑(List.ofFn f.val) : Multiset α).sort (· ≤ ·) = List.ofFn f.val := by
      rw [Multiset.coe_sort]
      exact List.mergeSort_eq_self (fun x y : α => x ≤ y) hsorted
    let l := (↑(List.ofFn f.val) : Multiset α).sort (· ≤ ·)
    have hl : l.length = n := by
      change ((↑(List.ofFn f.val) : Multiset α).sort (· ≤ ·)).length = n
      rw [hsort, List.length_ofFn]
    change List.ofFn (fun i : Fin n => l.get (Fin.cast hl.symm i)) = List.ofFn f.val
    rw [← List.ofFn_congr hl l.get, List.ofFn_get]
    exact hsort

/-- The actual monotone finite tuples have the native stars-and-bars cardinality. -/
theorem card_monotone_fin (n m : ℕ) :
    Fintype.card {f : Fin n → Fin m // Monotone f} = (m + n - 1).choose n := by
  rw [← Fintype.card_congr (sortedTupleEquiv (α := Fin m) n), card_sym_eq_choose,
    Fintype.card_fin]

end Sym
