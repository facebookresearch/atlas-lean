/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.Frobenius
import Mathlib.GroupTheory.Perm.Fin

/-! # Tests for `MathlibExt.GroupTheory.Frobenius` -/

namespace MathlibExtTest.GroupTheory.Frobenius

open MathlibExt.GroupTheory.FrobeniusWanted.GroupTheory Equiv

-- Test section: the general consequence. In a Frobenius action, the Frobenius kernel is closed
-- under multiplication: a product of two elements without fixed points is the identity or has
-- no fixed points.
example (G X : Type) [Group G] [Fintype G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X) (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (g h : G) (hg : ∀ x : X, g • x ≠ x) (hh : ∀ x : X, h • x ≠ x) :
    g * h = 1 ∨ ∀ x : X, (g * h) • x ≠ x := by
  obtain ⟨N, -, hN⟩ := frobenius_kernel_isNormal G X hcard htrans hstab hfrob
  have hmem : ∀ k : G, k ∈ N ↔ k = 1 ∨ ∀ x : X, k • x ≠ x := fun k => by
    rw [← SetLike.mem_coe, hN]
    rfl
  exact (hmem _).mp (N.mul_mem ((hmem g).mpr (Or.inr hg)) ((hmem h).mpr (Or.inr hh)))

-- Test section: the symmetric group `S₃` acting on three points is a Frobenius group.
private theorem transitive : ∀ x y : Fin 3, ∃ g : Perm (Fin 3), g • x = y :=
  fun x y => ⟨swap x y, by simp [Perm.smul_def]⟩

private theorem stabilizer_ne_bot : ∀ x : Fin 3, MulAction.stabilizer (Perm (Fin 3)) x ≠ ⊥ := by
  intro x
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  fin_cases x
  · exact ⟨⟨swap 1 2, by decide⟩, by decide⟩
  · exact ⟨⟨swap 0 2, by decide⟩, by decide⟩
  · exact ⟨⟨swap 0 1, by decide⟩, by decide⟩

private theorem fixes_at_most_one :
    ∀ g : Perm (Fin 3), g ≠ 1 → ∀ x y : Fin 3, g • x = x → g • y = y → x = y := by
  decide

-- Frobenius's theorem applied to `S₃`: its Frobenius kernel is a normal subgroup, which contains
-- the 3-cycle `finRotate 3` and not the transposition `swap 0 1` (it fixes `2`).
example : ∃ N : Subgroup (Perm (Fin 3)), N.Normal ∧ finRotate 3 ∈ N ∧ swap 0 1 ∉ N := by
  obtain ⟨N, hNormal, hN⟩ := frobenius_kernel_isNormal (Perm (Fin 3)) (Fin 3) (by simp)
    transitive stabilizer_ne_bot fixes_at_most_one
  have hmem : ∀ k : Perm (Fin 3), k ∈ N ↔ k = 1 ∨ ∀ x : Fin 3, k • x ≠ x := fun k => by
    rw [← SetLike.mem_coe, hN]
    rfl
  exact ⟨N, hNormal, (hmem _).mpr (by decide), fun h => absurd ((hmem _).mp h) (by decide)⟩

end MathlibExtTest.GroupTheory.Frobenius
