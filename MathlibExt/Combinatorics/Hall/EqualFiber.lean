/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card

/-!
# Hall's condition for the equal-label relation

Label the elements of two finite types by `f : A → K` and `g : B → K`, and relate `a` to `b` when
they carry the same label. Hall's condition for this relation (every finite `S ⊆ A` has at least
`#S` related elements of `B`) holds exactly when, for every label `k`, the fiber of `f` over `k`
is no larger than the fiber of `g` over `k`.

## Main results

* `Fintype.hall_equalFiber_iff_card_fibers`: Hall's condition for the equal-label relation is
  equivalent to the fiberwise inequality `#f⁻¹(k) ≤ #g⁻¹(k)`.

Combined with Hall's marriage theorem (`Fintype.all_card_le_filter_rel_iff_exists_injective`),
this gives a label-preserving injection `A → B` exactly when every fiber inequality holds.
-/

@[expose] public section

open Finset

namespace Fintype

variable {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq K]

/-- **Hall's condition for the equal-label relation.** For labelings `f : A → K` and
`g : B → K` of finite types, every `S : Finset A` has at least `#S` elements `b` with
`g b = f a` for some `a ∈ S` if and only if every fiber of `f` has at most as many elements as the
corresponding fiber of `g`.

This is the Hall condition of `Fintype.all_card_le_filter_rel_iff_exists_injective` for the
relation `fun a b => f a = g b`; a matching for it is a label-preserving injection. -/
theorem hall_equalFiber_iff_card_fibers
    (f : A -> K) (g : B -> K) :
    (forall S : Finset A, S.card <=
      (Finset.univ.filter fun b => exists a, a ∈ S /\ f a = g b).card) <->
      forall k : K, Fintype.card {a : A // f a = k} <=
        Fintype.card {b : B // g b = k} := by
  classical
  constructor
  · intro h k
    let S : Finset A := Finset.univ.filter fun a => f a = k
    by_cases hS : S.Nonempty
    · have hneighbor :
          (Finset.univ.filter fun b => exists a, a ∈ S /\ f a = g b) =
            Finset.univ.filter fun b => g b = k := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, haS, hab⟩
          have hak : f a = k := by simpa [S] using haS
          exact hab.symm.trans hak
        · intro hbk
          obtain ⟨a, haS⟩ := hS
          refine ⟨a, haS, ?_⟩
          have hak : f a = k := by simpa [S] using haS
          exact hak.trans hbk.symm
      have hhall := h S
      rw [hneighbor] at hhall
      simpa [S, Fintype.card_subtype] using hhall
    · have hempty : Fintype.card {a : A // f a = k} = 0 := by
        rw [Fintype.card_subtype]
        simpa [S] using Finset.not_nonempty_iff_eq_empty.mp hS
      rw [hempty]
      exact Nat.zero_le _
  · intro hfiber S
    let T : Finset K := S.image f
    have hneighbor :
        (Finset.univ.filter fun b => exists a, a ∈ S /\ f a = g b) =
          Finset.univ.filter fun b => g b ∈ T := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [T]
    rw [Finset.card_eq_sum_card_image f S, hneighbor,
      ← Finset.sum_card_fiberwise_eq_card_filter Finset.univ T g]
    apply Finset.sum_le_sum
    intro k hk
    calc
      (S.filter fun a => f a = k).card <=
          (Finset.univ.filter fun a => f a = k).card := by
        exact Finset.card_le_card (Finset.filter_subset_filter _ S.subset_univ)
      _ = Fintype.card {a : A // f a = k} := by
        rw [Fintype.card_subtype]
      _ <= Fintype.card {b : B // g b = k} := hfiber k
      _ = (Finset.univ.filter fun b => g b = k).card := by
        rw [Fintype.card_subtype]

end Fintype
