/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card










open Finset

namespace Fintype

variable {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq K]



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
