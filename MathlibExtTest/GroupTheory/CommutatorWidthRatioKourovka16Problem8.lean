/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8

open MathlibExt.GroupTheory.CommutatorWidthRatioKourovka16Problem8Wanted

-- Length zero permits exactly the empty product.
example {G : Type*} [Group G] (g : G) : IsProductOfCommutators 0 g ↔ g = 1 := by
  constructor
  · rintro ⟨l, hl, he⟩
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    simpa [this] using he.symm
  · rintro rfl
    exact ⟨[], by simp, by simp⟩

-- The minimum is taken over positive widths even for the trivial group.
example : commutatorWidth (Equiv.Perm (Fin 0)) = 1 := by
  let G := Equiv.Perm (Fin 0)
  have h : 1 ∈ {m : ℕ | 0 < m ∧ ∀ g ∈ commutator G, IsProductOfCommutators m g} :=
    ⟨by decide, fun g _ ↦ ⟨[], by simp, Subsingleton.elim _ _⟩⟩
  exact le_antisymm (Nat.sInf_le h) (Nat.sInf_mem ⟨_, h⟩).1

-- Two transpositions give a nonidentity element at the one-commutator bound.
example : ∃ g : Equiv.Perm (Fin 3), g ≠ 1 ∧ IsProductOfCommutators 1 g := by
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let b : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  exact ⟨a * b * a⁻¹ * b⁻¹, by decide, [(a, b)], by simp, by simp⟩
