/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # Subgroup closure commutation

Generatorwise commutation lifts to subgroup closures via centralizer
stability under closure.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G] {s t : Set G}

/-- If every element of `s` commutes with every element of `t`, then
`closure t` lies in the centralizer of `closure s`. -/
theorem closure_le_centralizer_closure_of_commute
    {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) :
    closure t ≤ centralizer (closure s) := by
  rw [centralizer_closure, closure_le]
  intro y hy
  exact mem_centralizer_iff.mpr fun x hx => (h x hx y hy).eq

/-- Elements of the closures of generatorwise commuting sets commute. -/
theorem commute_of_mem_closure
    {s t : Set G} {x y : G}
    (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y)
    (hx : x ∈ closure s) (hy : y ∈ closure t) :
    Commute x y := by
  have hle := closure_le_centralizer_closure_of_commute h
  have hy' : y ∈ centralizer (closure s) := hle hy
  have hm := mem_centralizer_iff.mp hy'
  rw [commute_iff_eq]
  exact hm x hx

end Subgroup
