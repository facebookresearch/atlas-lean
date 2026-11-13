/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Onsager.Torus
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant

open SimpleGraph

namespace StatMech.BeffaraDC

open StatMech.Onsager



theorem onsTorusGraph_eq_cycleGraph_boxProd (n : ℕ) [Fact (2 < n + 1)] :
    onsTorusGraph (n + 1) = cycleGraph (n + 1) □ cycleGraph (n + 1) := by
  ext u v
  simp only [onsTorusGraph, onsTorusAdj, boxProd_adj, cycleGraph_adj']
  change ((u.1 = v.1 ∧ (u.2 = v.2 + 1 ∨ u.2 = v.2 - 1)) ∨
      (u.2 = v.2 ∧ (u.1 = v.1 + 1 ∨ u.1 = v.1 - 1))) ↔
    ((((u.1 - v.1).val = 1 ∨ (v.1 - u.1).val = 1) ∧ u.2 = v.2) ∨
      (((u.2 - v.2).val = 1 ∨ (v.2 - u.2).val = 1) ∧ u.1 = v.1))
  have hn2 : 2 < n + 1 := Fact.out
  have hn : 0 < n := by omega
  have hval {a b : ZMod (n + 1)} :
      (a - b).val = 1 ↔ a = b + 1 := by
    have hone : (1 : Fin (n + 1)).val = 1 := by
      simp [hn]
    constructor
    · intro h
      have heq : a - b = (1 : Fin (n + 1)) := by
        apply Fin.ext
        exact h.trans hone.symm
      exact (sub_eq_iff_eq_add').mp heq
    · intro h
      have heq : a - b = (1 : Fin (n + 1)) :=
        (sub_eq_iff_eq_add').mpr h
      have := congrArg Fin.val heq
      exact this.trans hone
  rw [hval (a := u.1) (b := v.1), hval (a := v.1) (b := u.1),
    hval (a := u.2) (b := v.2), hval (a := v.2) (b := u.2)]
  constructor
  · rintro (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
    · exact Or.inr ⟨Or.inl h1, h0⟩
    · exact Or.inr ⟨Or.inr (by linear_combination -h1), h0⟩
    · exact Or.inl ⟨Or.inl h0, h1⟩
    · exact Or.inl ⟨Or.inr (by linear_combination -h0), h1⟩
  · rintro (⟨h0 | h0, h1⟩ | ⟨h1 | h1, h0⟩)
    · exact Or.inr ⟨h1, Or.inl h0⟩
    · exact Or.inr ⟨h1, Or.inr (by linear_combination -h0)⟩
    · exact Or.inl ⟨h0, Or.inl h1⟩
    · exact Or.inl ⟨h0, Or.inr (by linear_combination -h1)⟩



theorem onsTorusGraph_connected (L : ℕ) [Fact (2 < L)] :
    (onsTorusGraph L).Connected := by
  cases L with
  | zero =>
      exfalso
      exact (Nat.not_lt_zero 2) (Fact.out : 2 < 0)
  | succ n =>
      rw [onsTorusGraph_eq_cycleGraph_boxProd n]
      exact cycleGraph_connected.boxProd cycleGraph_connected

end StatMech.BeffaraDC
