/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Component halving

If every merged label is shared by at least two old
components, the number of components at most halves. This
is the counting step of Boruvka's algorithm; the graph
phases are not included here.
-/

@[expose] public section

/-- Component halving (ALG-52 Boruvka core). If every
component label is shared with a different vertex (each
component selects an outgoing edge to another component,
so after merging each group has at least two old
components), the number of merged components is at most
half the number of vertices, in counting form. -/
theorem boruvka_halving {C : Type*} [Fintype C] [DecidableEq C]
    (f : C → C) (hf : ∀ c, ∃ d, d ≠ c ∧ f d = f c) :
    2 * (Finset.univ.image f).card ≤ Fintype.card C := by
  have h2 : ∀ y ∈ Finset.univ.image f,
      2 ≤ (Finset.univ.filter (fun a => f a = y)).card := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d, hdne, hdf⟩ := hf c
    have hc : c ∈ Finset.univ.filter (fun a => f a = f c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, rfl⟩
    have hd : d ∈ Finset.univ.filter (fun a => f a = f c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ d, hdf⟩
    have hlt : 1 < (Finset.univ.filter (fun a => f a = f c)).card :=
      Finset.one_lt_card.mpr ⟨c, hc, d, hd, Ne.symm hdne⟩
    omega
  have hcard : Fintype.card C =
      ∑ y ∈ Finset.univ.image f, (Finset.univ.filter (fun a => f a = y)).card :=
    Finset.card_univ.trans (Finset.card_eq_sum_card_image f Finset.univ)
  calc 2 * (Finset.univ.image f).card
      = ∑ _y ∈ Finset.univ.image f, 2 := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ y ∈ Finset.univ.image f,
        (Finset.univ.filter (fun a => f a = y)).card :=
        Finset.sum_le_sum h2
    _ = Fintype.card C := hcard.symm

end
