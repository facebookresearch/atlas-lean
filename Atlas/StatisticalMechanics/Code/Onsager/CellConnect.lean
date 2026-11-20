/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEuler










namespace StatMech.Onsager.CellConnect

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler



theorem card_inter_eq_sum (S T : Finset (ℤ × ℤ)) :
    ((S ∩ T).card : ℤ) = ∑ t ∈ T, (if t ∈ S then (1 : ℤ) else 0) := by
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]


private theorem sum_ite_quad (S : Finset (ℤ × ℤ)) (a b c d : ℤ × ℤ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∑ t ∈ ({a, b, c, d} : Finset (ℤ × ℤ)), (if t ∈ S then (1 : ℤ) else 0))
      = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0)
        + (if c ∈ S then 1 else 0) + (if d ∈ S then 1 else 0) := by
  rw [Finset.sum_insert (by simp only [mem_insert, mem_singleton]; tauto),
      Finset.sum_insert (by simp only [mem_insert, mem_singleton]; tauto),
      Finset.sum_insert (by simp only [mem_singleton]; exact hcd),
      Finset.sum_singleton]
  ring




theorem cornerCount_BL (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    (cornerCount S (x, y) : ℤ)
      = (if (x - 1, y) ∈ S then 1 else 0) + (if (x, y - 1) ∈ S then 1 else 0)
        + (if (x - 1, y - 1) ∈ S then 1 else 0) := by
  have hset : (({(x, y), ((x, y).1 - 1, (x, y).2), ((x, y).1, (x, y).2 - 1),
        ((x, y).1 - 1, (x, y).2 - 1)}) : Finset (ℤ × ℤ))
      = {(x, y), (x - 1, y), (x, y - 1), (x - 1, y - 1)} := rfl
  rw [cornerCount_eq_inter, hset, card_inter_eq_sum,
      sum_ite_quad S (x, y) (x - 1, y) (x, y - 1) (x - 1, y - 1)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega),
      if_neg hc]
  ring


theorem cornerCount_BR (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    (cornerCount S (x + 1, y) : ℤ)
      = (if (x + 1, y) ∈ S then 1 else 0) + (if (x + 1, y - 1) ∈ S then 1 else 0)
        + (if (x, y - 1) ∈ S then 1 else 0) := by
  have hset : (({(x + 1, y), ((x + 1, y).1 - 1, (x + 1, y).2), ((x + 1, y).1, (x + 1, y).2 - 1),
        ((x + 1, y).1 - 1, (x + 1, y).2 - 1)}) : Finset (ℤ × ℤ))
      = {(x + 1, y), (x, y), (x + 1, y - 1), (x, y - 1)} := by norm_num
  rw [cornerCount_eq_inter, hset, card_inter_eq_sum,
      sum_ite_quad S (x + 1, y) (x, y) (x + 1, y - 1) (x, y - 1)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega),
      if_neg hc]
  ring


theorem cornerCount_TL (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    (cornerCount S (x, y + 1) : ℤ)
      = (if (x, y + 1) ∈ S then 1 else 0) + (if (x - 1, y + 1) ∈ S then 1 else 0)
        + (if (x - 1, y) ∈ S then 1 else 0) := by
  have hset : (({(x, y + 1), ((x, y + 1).1 - 1, (x, y + 1).2), ((x, y + 1).1, (x, y + 1).2 - 1),
        ((x, y + 1).1 - 1, (x, y + 1).2 - 1)}) : Finset (ℤ × ℤ))
      = {(x, y + 1), (x - 1, y + 1), (x, y), (x - 1, y)} := by norm_num
  rw [cornerCount_eq_inter, hset, card_inter_eq_sum,
      sum_ite_quad S (x, y + 1) (x - 1, y + 1) (x, y) (x - 1, y)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega),
      if_neg hc]
  ring


theorem cornerCount_TR (S : Finset (ℤ × ℤ)) (x y : ℤ) (hc : (x, y) ∉ S) :
    (cornerCount S (x + 1, y + 1) : ℤ)
      = (if (x + 1, y + 1) ∈ S then 1 else 0) + (if (x, y + 1) ∈ S then 1 else 0)
        + (if (x + 1, y) ∈ S then 1 else 0) := by
  have hset : (({(x + 1, y + 1), ((x + 1, y + 1).1 - 1, (x + 1, y + 1).2),
        ((x + 1, y + 1).1, (x + 1, y + 1).2 - 1), ((x + 1, y + 1).1 - 1, (x + 1, y + 1).2 - 1)})
        : Finset (ℤ × ℤ))
      = {(x + 1, y + 1), (x, y + 1), (x + 1, y), (x, y)} := by norm_num
  rw [cornerCount_eq_inter, hset, card_inter_eq_sum,
      sum_ite_quad S (x + 1, y + 1) (x, y + 1) (x + 1, y) (x, y)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega)
        (by simp only [ne_eq, Prod.mk.injEq]; omega) (by simp only [ne_eq, Prod.mk.injEq]; omega),
      if_neg hc]
  ring

end StatMech.Onsager.CellConnect
