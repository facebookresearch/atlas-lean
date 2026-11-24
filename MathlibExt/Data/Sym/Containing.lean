/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Multiset.AddSub

/-!
# Exact symmetric-power cardinality with an original required submultiset

Subtracting the actual required multiset is a bijection, with inverse
addition of that same multiset. The original cardinality equality gives
the remaining length. Native stars-and-bars then counts compatible cuts.
No counting or containment certificate is supplied.
-/

@[expose] public section
noncomputable section

namespace Sym

universe u

variable {α : Type u}

/-- Symmetric words containing the original fixed submultiset are exactly the remaining symmetric words. -/
def containingFixedEquiv (t : Multiset α) (k : ℕ) :
    {s : Sym α (k + t.card) // t ≤ s.val} ≃ Sym α k := by
  classical
  exact
    { toFun := fun s => ⟨s.val.val - t, by
        rw [Multiset.card_sub s.property, s.val.property]
        omega⟩
      invFun := fun s =>
        ⟨⟨s.val + t, by rw [Multiset.card_add, s.property]⟩, Multiset.le_add_left t s.val⟩
      left_inv := fun s => by
        apply Subtype.ext
        apply Subtype.ext
        exact Multiset.sub_add_cancel s.property
      right_inv := fun s => by
        apply Subtype.ext
        exact Multiset.add_sub_cancel_right }

/-- Native stars-and-bars counts the actual compatible cuts, including the empty incompatible case. -/
theorem card_containing_fixed_fin (n m : ℕ) (t : Multiset (Fin (n + 1))) (ht : t.card ≤ n) :
    Fintype.card {s : Sym (Fin (n + 1)) m // t ≤ s.val} = (n + m - t.card).choose n := by
  classical
  by_cases hm : t.card ≤ m
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + t.card :=
      ⟨m - t.card, (Nat.sub_add_cancel hm).symm⟩
    subst m
    rw [Fintype.card_congr (containingFixedEquiv t k), Sym.card_sym_eq_choose, Fintype.card_fin]
    have hleft : n + 1 + k - 1 = n + k := by omega
    have hright : n + (k + t.card) - t.card = n + k := by omega
    rw [hleft, hright]
    exact (Nat.choose_symm_add (a := n) (b := k)).symm
  · have hempty : IsEmpty {s : Sym (Fin (n + 1)) m // t ≤ s.val} :=
      ⟨fun s => hm (by
        have h := Multiset.card_le_card s.property
        simpa only [s.val.property] using h)⟩
    letI := hempty
    rw [Fintype.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega : n + m - t.card < n)]

end Sym
