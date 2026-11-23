/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modified for Atlas by Meta Platforms, Inc.: generalized prescribed-coordinate counts to
dependent finite products and exposed direct cardinality formulas for finite function types.
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-! # Finite functions with prescribed coordinates

This file counts functions whose values are prescribed on a finite set of coordinates.  The
dependent result extends `Fintype.card_filter_piFinset_eq_of_mem` from one coordinate to a
`Finset`; its constant-family specializations give both the direct count and a division-free
multiplicative identity.

Adapted from `Groundwork.Colouring.card_prescribed` in
`eth/proof/networks/Groundwork/Net/Colouring.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Fintype

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → DecidableEq (α i)]

/-- The number of dependent functions in `piFinset s` with prescribed values on `S` is the
product of the numbers of choices outside `S`. -/
theorem card_filter_piFinset_eqOn_of_mem (s : (i : ι) → Finset (α i)) (S : Finset ι)
    (f : (i : {i // i ∈ S}) → α i.1) (hf : ∀ i, f i ∈ s i.1) :
    {g ∈ piFinset s | ∀ i, g i.1 = f i}.card =
      ∏ i ∈ Finset.univ \ S, (s i).card := by
  have h : {g ∈ piFinset s | ∀ i, g i.1 = f i} =
      piFinset (fun i => if hi : i ∈ S then {f ⟨i, hi⟩} else s i) := by
    ext g
    simp only [Finset.mem_filter, mem_piFinset]
    constructor
    · rintro ⟨hg, heq⟩ i
      by_cases hi : i ∈ S
      · simp [hi, heq ⟨i, hi⟩]
      · simpa [hi] using hg i
    · intro hg
      constructor
      · intro i
        by_cases hi : i ∈ S
        · have heq : g i = f ⟨i, hi⟩ := by simpa [hi] using hg i
          rw [heq]
          exact hf ⟨i, hi⟩
        · simpa [hi] using hg i
      · intro i
        simpa [i.2] using hg i.1
  rw [h, card_piFinset]
  calc
    (∏ i, (if hi : i ∈ S then {f ⟨i, hi⟩} else s i).card) =
        ∏ i, if i ∈ S then 1 else (s i).card := by
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> simp
    _ = ∏ i ∈ Finset.univ \ S, (s i).card := by
      rw [Finset.sdiff_eq_filter, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [hi]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The number of functions agreeing with `f` on `S` is the number of unrestricted choices on
the remaining coordinates. -/
theorem card_filter_univ_eqOn (S : Finset ι) (f : {i // i ∈ S} → κ) :
    (Finset.univ.filter fun g : ι → κ => ∀ i, g i.1 = f i).card =
      Fintype.card κ ^ (Fintype.card ι - S.card) := by
  simpa [Finset.card_sdiff] using
    card_filter_piFinset_eqOn_of_mem (fun _ => (Finset.univ : Finset κ)) S f (by simp)

/-- Division-free count of finite functions with prescribed values on a set of coordinates. -/
theorem card_filter_univ_eqOn_mul_pow_card (S : Finset ι) (f : {i // i ∈ S} → κ) :
    (Finset.univ.filter fun g : ι → κ => ∀ i, g i.1 = f i).card *
      Fintype.card κ ^ S.card =
      Fintype.card κ ^ Fintype.card ι := by
  rw [card_filter_univ_eqOn]
  exact Nat.pow_sub_mul_pow _ (Finset.card_le_univ S)

end Fintype
