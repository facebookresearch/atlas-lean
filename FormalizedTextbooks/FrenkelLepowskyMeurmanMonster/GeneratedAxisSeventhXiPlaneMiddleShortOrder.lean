/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortArithmeticData
public import Mathlib.Data.List.Sort

/-! Ordered physical coordinates identify genuine finite catalogue enumerations. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A strictly increasing enumeration with the correct support is the actual ordered catalogue. -/
theorem generatedSeventhXi_ordered_coordinates {α : Type*} [LinearOrder α]
    (s : Finset α) {n : ℕ} (hn : s.card = n) (v : Fin n → α)
    (hv : StrictMono v) (hs : ∀ x, x ∈ s ↔ ∃ k, v k = x) (k : Fin n) :
    (s.orderIsoOfFin hn k).val = v k := by
  have he : s.sort = List.ofFn v := by
    apply s.sortedLT_sort.eq_of_mem_iff hv.sortedLT_ofFn
    intro x
    rw [Finset.mem_sort, List.mem_ofFn]
    exact hs x
  rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [he]
  change (List.ofFn v).get ⟨k.val, by simp⟩ = v k
  rw [List.get_ofFn]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
