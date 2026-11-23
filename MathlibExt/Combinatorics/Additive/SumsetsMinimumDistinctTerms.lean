/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Sums of distinct residues in a cyclic group

Bajnok's lemma realizes every residue modulo `d` as a sum of `t` distinct residues
for each `0 < t < d`.
-/

namespace MetaMathlibExt

open Finset

/-- **Bajnok's lemma on subset sums in $\mathbb{Z}/d\mathbb{Z}$.** Let $d$ and $t$ be natural
numbers with $1 \le t \le d - 1$. Then every $\ell \in \mathbb{Z}/d\mathbb{Z}$ is the sum of the
elements of some $t$-element subset $L \subseteq \mathbb{Z}/d\mathbb{Z}$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 1 (Bajnok) (`integers-2025-A12-lem-1`). -/
public theorem exists_card_eq_sum_eq_zmod (d t : ℕ) (ht : 1 ≤ t) (htd : t ≤ d - 1)
    (ℓ : ZMod d) :
    ∃ L : Finset (ZMod d), L.card = t ∧ L.sum id = ℓ := by
  have : NeZero d := ⟨by omega⟩
  let I := range (t + 1)
  let S := ∑ i ∈ I, (i : ZMod d)
  -- Erasing the remainder and translating by minus the quotient subtracts the whole offset.
  let n := (S - ℓ).val
  let r := n % t
  let q := n / t
  have hr : r ∈ I := mem_range.mpr ((Nat.mod_lt n ht).trans (Nat.lt_succ_self t))
  have hcard : (I.erase r).card = t := by simp [card_erase_of_mem hr, I]
  have hlt {i : ℕ} (hi : i ∈ I.erase r) : i < d := by
    have := mem_range.mp (mem_of_mem_erase hi : i ∈ I)
    omega
  let shift (i : ℕ) := (i : ZMod d) - q
  have hinj : Set.InjOn shift (I.erase r) := by
    intro a ha b hb hab
    exact CharP.natCast_injOn_Iio (ZMod d) d (hlt ha) (hlt hb) (sub_left_inj.mp hab)
  refine ⟨(I.erase r).image shift, (card_image_of_injOn hinj).trans hcard, ?_⟩
  simp only [sum_image hinj, id_eq, shift, sum_sub_distrib]
  rw [sum_erase_eq_sub hr, sum_const, hcard, nsmul_eq_mul, sub_sub, ← Nat.cast_mul,
    ← Nat.cast_add, Nat.mod_add_div, ZMod.natCast_zmod_val, sub_sub_cancel]

end MetaMathlibExt
