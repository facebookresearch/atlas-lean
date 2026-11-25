/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting units of a given order

The number of units of order `L` modulo a positive integer is divisible by the totient of `L`.
-/

public section

namespace MetaMathlibExt

/-- **The number of units of order $L$ is a multiple of $\varphi(L)$.** For natural numbers
$n \ge 1$ and $L$, the number $E(L, n)$ of elements of order $L$ in the unit group
$(\mathbb{Z}/n\mathbb{Z})^\times$ is divisible by Euler's totient $\varphi(L)$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 4 (`integers-2025-A26-cor-4`). -/
theorem totient_dvd_card_orderOf_eq (L n : ℕ) [NeZero n] : L.totient ∣
    (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = L).card := by
  classical
  -- Partition the units of order L by the subgroup they generate.
  rw [Finset.card_eq_sum_card_image Subgroup.zpowers]
  apply Finset.dvd_sum
  intro H hH
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hH
  have hgL : orderOf g = L := (Finset.mem_filter.mp hg).2
  have hcard : L ∣ Fintype.card (Subgroup.zpowers g) := by
    rw [Fintype.card_zpowers, hgL]
  rw [← IsCyclic.card_orderOf_eq_totient hcard]
  apply dvd_of_eq
  -- The inclusion identifies the elements of order L in this subgroup with the fiber.
  apply Finset.card_bij (fun (u : Subgroup.zpowers g) _ ↦ u.val)
  · intro u hu
    have huL : orderOf u.val = L := (Subgroup.orderOf_coe u).trans (Finset.mem_filter.mp hu).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, huL]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.property)
      (by simp only [Nat.card_zpowers, hgL, huL, le_refl])
  · exact fun _ _ _ _ h ↦ Subtype.ext h
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have humem : u ∈ Subgroup.zpowers g := hu.2 ▸ Subgroup.mem_zpowers u
    refine ⟨⟨u, humem⟩, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.orderOf_mk] using hu.1

end MetaMathlibExt
