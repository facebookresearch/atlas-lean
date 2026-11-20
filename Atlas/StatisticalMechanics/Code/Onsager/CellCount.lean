/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace StatMech.Onsager.CellCount

open Finset


def cornersOf (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {c, (c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 + 1, c.2 + 1)}


def cornerCount (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℕ :=
  (S.filter (fun c => v ∈ cornersOf c)).card


def cellVerts (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.biUnion cornersOf


theorem cornersOf_card (c : ℤ × ℤ) : (cornersOf c).card = 4 := by
  unfold cornersOf
  rw [Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_singleton, Prod.ext_iff]; omega),
      card_singleton]


theorem mem_cornersOf_iff (c v : ℤ × ℤ) :
    v ∈ cornersOf c ↔
      c = v ∨ c = (v.1 - 1, v.2) ∨ c = (v.1, v.2 - 1) ∨ c = (v.1 - 1, v.2 - 1) := by
  obtain ⟨cx, cy⟩ := c
  obtain ⟨vx, vy⟩ := v
  unfold cornersOf
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega


private def candCells (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)}

theorem cornerCount_le_four (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    cornerCount S v ≤ 4 := by
  unfold cornerCount
  have hsub : S.filter (fun c => v ∈ cornersOf c) ⊆ candCells v := by
    intro c hc
    rw [mem_filter, mem_cornersOf_iff] at hc
    unfold candCells
    simp only [mem_insert, mem_singleton]
    tauto
  refine (card_le_card hsub).trans ?_
  unfold candCells
  refine (card_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_insert_le _ _) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1).trans ?_
  simp



theorem sum_cornerCount (S : Finset (ℤ × ℤ)) :
    ∑ v ∈ cellVerts S, cornerCount S v = 4 * S.card := by
  unfold cornerCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ c ∈ S, (∑ v ∈ cellVerts S, if v ∈ cornersOf c then 1 else 0) = 4 := by
    intro c hc
    rw [← Finset.sum_filter]
    have hfe : (cellVerts S).filter (fun v => v ∈ cornersOf c) = cornersOf c := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hv
        exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, hv⟩, hv⟩
    rw [hfe, Finset.sum_const, smul_eq_mul, mul_one]
    exact cornersOf_card c
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]

end StatMech.Onsager.CellCount
