/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modified for Atlas by Meta Platforms, Inc.: extracted generic finite-fiber transport results,
used Mathlib's canonical fiber equivalence, and added arbitrary finite-carrier density transfer.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-! # Transport through finite fibers

Equal fiber cardinalities let one finite labeling be transported to another by a permutation and
let density bounds be pulled back through a map on arbitrary finite carriers.

Adapted from `ClauseBound.Group.Grouping.exists_perm_of_fiber` and
`ClauseBound.Group.Grouping.card_filter_le_of_fibers` in
`eth/proof/rates/ClauseBound/Group/Grouping.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Fintype

/-- Two labelings of a finite type with equally sized fibers differ by a permutation. -/
theorem exists_perm_of_fiber {V C : Type*} [Fintype V] [DecidableEq C]
    (α β : V → C)
    (h : ∀ y, Fintype.card {x // α x = y} = Fintype.card {x // β x = y}) :
    ∃ p : Equiv.Perm V, ∀ x, β (p x) = α x := by
  let e : (y : C) → {x // α x = y} ≃ {x // β x = y} := fun y =>
    Fintype.equivOfCardEq (h y)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

end Fintype

namespace Finset

/-- A density bound transfers through a map whose fibers over the target carrier all have the
same cardinality. -/
theorem card_filter_le_of_fibers {Ω X : Type*} [DecidableEq X]
    (Ωs : Finset Ω) (f : Ω → X) (Xs : Finset X) (hf : Set.MapsTo f Ωs Xs)
    (hconst : ∀ x ∈ Xs, ∀ x' ∈ Xs,
      (Ωs.filter fun e => f e = x).card ≤ (Ωs.filter fun e => f e = x').card)
    (Q : X → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : ((Xs.filter Q).card : ℝ) ≤ ε * Xs.card) :
    ((Ωs.filter fun e => Q (f e)).card : ℝ) ≤ ε * Ωs.card := by
  rcases Xs.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hΩs : Ωs = ∅ := eq_empty_iff_forall_notMem.2 fun e he => by
      simpa using hf he
    subst Ωs
    simp
  · have hfiber : ∀ x ∈ Xs, (Ωs.filter fun e => f e = x).card =
        (Ωs.filter fun e => f e = x₀).card := fun x hx =>
      le_antisymm (hconst x hx x₀ hx₀) (hconst x₀ hx₀ x hx)
    have hΩs : Ωs.card = Xs.card * (Ωs.filter fun e => f e = x₀).card := by
      rw [card_eq_sum_card_fiberwise hf, sum_congr rfl hfiber, sum_const,
        Nat.nsmul_eq_mul]
    have hQcard : (Ωs.filter fun e => Q (f e)).card =
        (Xs.filter Q).card * (Ωs.filter fun e => f e = x₀).card := by
      rw [card_eq_sum_card_fiberwise (f := f) (t := Xs.filter Q) (by
        intro e he
        have he' : e ∈ Ωs ∧ Q (f e) := by simpa using he
        simpa using ⟨hf he'.1, he'.2⟩), ← Nat.nsmul_eq_mul, ← sum_const]
      refine sum_congr rfl fun x hx => ?_
      rw [← hfiber x (mem_filter.1 hx).1, filter_filter]
      congr 1
      refine filter_congr fun e _ => ?_
      exact ⟨fun h => h.2, fun h => ⟨h ▸ (mem_filter.1 hx).2, h⟩⟩
    rw [hΩs, hQcard]
    simp only [Nat.cast_mul]
    calc
      ((Xs.filter Q).card : ℝ) * (Ωs.filter fun e => f e = x₀).card ≤
          (ε * Xs.card) * (Ωs.filter fun e => f e = x₀).card :=
        mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg _)
      _ = ε * (Xs.card * (Ωs.filter fun e => f e = x₀).card) := by
        rw [mul_assoc]

end Finset
