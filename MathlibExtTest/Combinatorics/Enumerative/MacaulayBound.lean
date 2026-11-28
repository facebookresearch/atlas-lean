/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MacaulayBound

@[expose] public section

-- Consumer with the original binders.
example (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card :=
  Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem n d hd B hB C hC hCB

-- Boundary: the bound fails in degree `d = 0`. In one variable, `B = {1}` and `C = {x}`
-- satisfy the divisor condition, but `#C = 1 > 0 = Nat.macaulayPow 0 #B`.
example : ¬ ∀ (B C : Finset (Fin 1 →₀ ℕ)), (∀ m ∈ B, m.degree = 0) →
    (∀ u ∈ C, u.degree = 0 + 1) →
    (∀ u ∈ C, ∀ i : Fin 1, 1 ≤ u i → u - Finsupp.single i 1 ∈ B) →
    C.card ≤ Nat.macaulayPow 0 B.card := by
  intro h
  have := h {0} {Finsupp.single 0 1} (by simp) (by simp) (by
    intro u hu i _
    rw [Finset.mem_singleton] at hu ⊢
    subst hu
    rw [Subsingleton.elim i 0, tsub_self])
  simp at this
