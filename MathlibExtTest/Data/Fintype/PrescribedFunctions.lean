/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Data.Fintype.PrescribedFunctions
import Mathlib.Tactic.NormNum

open Finset

example {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι]
    [(i : ι) → DecidableEq (α i)] (s : (i : ι) → Finset (α i))
    (S : Finset ι) (f : (i : ι) → α i) (hf : ∀ i ∈ S, f i ∈ s i) :
    {g ∈ Fintype.piFinset s | ∀ i ∈ S, g i = f i}.card =
      ∏ i ∈ univ \ S, (s i).card :=
  Fintype.card_filter_piFinset_eqOn_of_mem s S f hf

-- The general result specializes to Mathlib's existing one-coordinate API.
example {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι]
    [(i : ι) → DecidableEq (α i)] (s : (i : ι) → Finset (α i))
    (i : ι) (f : (i : ι) → α i) (hf : f i ∈ s i) :
    {g ∈ Fintype.piFinset s | g i = f i}.card =
      ∏ j ∈ univ.erase i, (s j).card := by
  simpa [Finset.sdiff_singleton_eq_erase] using
    Fintype.card_filter_piFinset_eqOn_of_mem s {i} f (by simpa)

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : Finset ι) (f : ι → κ) :
    (univ.filter fun g : ι → κ => ∀ i ∈ S, g i = f i).card =
      Fintype.card κ ^ (Fintype.card ι - S.card) :=
  Fintype.card_filter_univ_eqOn S f

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : Finset ι) (f : ι → κ) :
    (univ.filter fun g : ι → κ => ∀ i ∈ S, g i = f i).card *
      Fintype.card κ ^ S.card =
      Fintype.card κ ^ Fintype.card ι :=
  Fintype.card_filter_univ_eqOn_mul_pow_card S f

-- One prescribed coordinate leaves four of the eight functions `Fin 3 → Bool`.
example : (univ.filter fun g : Fin 3 → Bool =>
    ∀ i ∈ ({0} : Finset (Fin 3)), g i = true).card = 4 := by
  convert Fintype.card_filter_univ_eqOn ({0} : Finset (Fin 3)) (fun _ => true) using 1 <;>
    norm_num

-- Two coordinates receive different prescribed values.
example : (univ.filter fun g : Fin 3 → Bool => ∀ i ∈ ({0, 2} : Finset (Fin 3)),
    g i = if i = 0 then true else false).card = 2 := by
  convert Fintype.card_filter_univ_eqOn ({0, 2} : Finset (Fin 3))
      (fun i => if i = 0 then true else false) using 1 <;>
    norm_num

-- Prescribing all four coordinates leaves one function.
example : (univ.filter fun g : Fin 4 → Bool => ∀ i ∈ (univ : Finset (Fin 4)),
    g i = decide (i.val % 2 = 0)).card = 1 := by
  convert Fintype.card_filter_univ_eqOn (univ : Finset (Fin 4))
      (fun i => decide (i.val % 2 = 0)) using 1 <;>
    norm_num

-- Prescribing no coordinates leaves every function.
example : (univ.filter fun g : Fin 3 → Bool =>
    ∀ i ∈ (∅ : Finset (Fin 3)), g i = true).card = 8 := by
  convert Fintype.card_filter_univ_eqOn (∅ : Finset (Fin 3)) (fun _ => true) using 1 <;>
    norm_num

-- There is one function between empty types, and the multiplicative identity uses `0 ^ 0 = 1`.
example : (univ.filter fun g : Fin 0 → Fin 0 =>
    ∀ i ∈ (∅ : Finset (Fin 0)), g i = Fin.elim0 i).card = 1 := by
  convert Fintype.card_filter_univ_eqOn (∅ : Finset (Fin 0))
      (fun i : Fin 0 => (Fin.elim0 i : Fin 0)) using 1 <;>
    norm_num

example : (univ.filter fun g : Fin 0 → Fin 0 =>
    ∀ i ∈ (∅ : Finset (Fin 0)), g i = Fin.elim0 i).card *
      Fintype.card (Fin 0) ^ (∅ : Finset (Fin 0)).card =
      Fintype.card (Fin 0) ^ Fintype.card (Fin 0) :=
  Fintype.card_filter_univ_eqOn_mul_pow_card ∅ fun i => Fin.elim0 i

-- No prescribed total function exists from a nonempty type to an empty one.
example : IsEmpty (Fin 1 → Fin 0) := ⟨fun f => Fin.elim0 (f 0)⟩

-- The source's one-coordinate statement is a direct client of the generic result.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (a : ι) (γ : κ) :
    (univ.filter fun g : ι → κ => g a = γ).card * Fintype.card κ =
      Fintype.card κ ^ Fintype.card ι := by
  simpa using Fintype.card_filter_univ_eqOn_mul_pow_card ({a} : Finset ι) (fun _ => γ)

-- The source's two-coordinate statement permits different prescribed values.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {a b : ι} (hab : a ≠ b) (γ γ' : κ) :
    (univ.filter fun g : ι → κ => g a = γ ∧ g b = γ').card * Fintype.card κ ^ 2 =
      Fintype.card κ ^ Fintype.card ι := by
  have h := Fintype.card_filter_univ_eqOn_mul_pow_card ({a, b} : Finset ι)
    (fun i => if i = a then γ else γ')
  rw [card_pair hab] at h
  simpa [hab.symm] using h

-- The source's four-coordinate statement uses two nonuniform prescribed values.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {a b a' b' : ι} (hab : a ≠ b) (h1 : a ≠ a') (h2 : a ≠ b')
    (h3 : b ≠ a') (h4 : b ≠ b') (h5 : a' ≠ b') (γ γ' : κ) :
    (univ.filter fun g : ι → κ =>
      (g a = γ ∧ g b = γ') ∧ (g a' = γ ∧ g b' = γ')).card *
      Fintype.card κ ^ 4 = Fintype.card κ ^ Fintype.card ι := by
  have h := Fintype.card_filter_univ_eqOn_mul_pow_card ({a, b, a', b'} : Finset ι)
    (fun i => if i = a ∨ i = a' then γ else γ')
  have hc : #({a, b, a', b'} : Finset ι) = 4 := by
    rw [card_insert_of_notMem (by simp [hab, h1, h2]),
      card_insert_of_notMem (by simp [h3, h4]), card_pair h5]
  rw [hc] at h
  simpa [hab.symm, h1.symm, h2.symm, h3, h3.symm, h4.symm, h5.symm, and_assoc] using h

#print axioms Fintype.card_filter_piFinset_eqOn_of_mem
#print axioms Fintype.card_filter_univ_eqOn
#print axioms Fintype.card_filter_univ_eqOn_mul_pow_card
