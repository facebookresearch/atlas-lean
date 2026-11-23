/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.OrderIsoNat
import MathlibExt.Combinatorics.AccessibleSets

/-! # Tests for accessibility and its partition property -/

namespace MetaMathlibExt.accessible_union_partition

-- Enumerating an infinite color class in order witnesses accessibility of all positive gaps.
example : IsAccessible (Set.Ioi 0) := by
  intro r hr
  refine ⟨Set.Subset.rfl, hr, ?_⟩
  intro c k _
  obtain ⟨color, hinf⟩ := Finite.exists_infinite_fiber (fun n : ℕ => c n.succPNat)
  let e := Nat.Subtype.orderIsoOfNat ((fun n : ℕ => c n.succPNat) ⁻¹' {color})
  have hc (i : ℕ) : c (e i).val.succPNat = color := (e i).property
  refine ⟨fun i => (e i).val.succPNat, fun i j => (hc i).trans (hc j).symm, ?_⟩
  intro i hi
  have hlt : (e i).val < (e (i + 1)).val := e.strictMono (Nat.lt_succ_self i)
  exact ⟨(e (i + 1)).val - (e i).val, Nat.sub_pos_of_lt hlt, by simp⟩

-- In the parity partition of an accessible set, the even gaps must be accessible.
example {D : Set ℕ} (hD : IsAccessible D) : IsAccessible {d ∈ D | d % 2 = 0} := by
  have hsplit : D = {d ∈ D | d % 2 = 1} ∪ {d ∈ D | d % 2 = 0} := by
    ext d
    change d ∈ D ↔ (d ∈ D ∧ d % 2 = 1) ∨ (d ∈ D ∧ d % 2 = 0)
    rw [← and_or_left]
    exact ⟨fun hd => ⟨hd, by omega⟩, And.left⟩
  apply (accessible_union_partition _ _ _ hsplit hD).resolve_left
  intro hodd
  let parity (a : ℕ+) : Fin 2 := ⟨(a : ℕ) % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨x, hc, hdiff⟩ := (hodd 2 (by decide)).2.2 parity 2 (by decide)
  obtain ⟨d, ⟨_, hd⟩, hgap⟩ := hdiff 0 (by decide)
  have heq : (x 0 : ℕ) % 2 = (x 1 : ℕ) % 2 := congrArg Fin.val (hc 0 1)
  change (x 1 : ℤ) - (x 0 : ℤ) = d at hgap
  omega

end MetaMathlibExt.accessible_union_partition
