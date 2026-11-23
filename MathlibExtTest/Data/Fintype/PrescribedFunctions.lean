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

private def EmptyUnprescribedFiber : Bool → Type
  | false => Empty
  | true => Unit

private instance (i : Bool) : Fintype (EmptyUnprescribedFiber i) := by
  cases i <;> simp [EmptyUnprescribedFiber] <;> infer_instance

private instance (i : Bool) : DecidableEq (EmptyUnprescribedFiber i) := by
  cases i <;> simp [EmptyUnprescribedFiber] <;> infer_instance

private def prescribedUnit
    (i : {i // i ∈ ({true} : Finset Bool)}) : EmptyUnprescribedFiber i.1 := by
  rcases i with ⟨i, hi⟩
  cases i
  · simp at hi
  · exact ()

-- A prescription on `true` does not require an element of the empty `false` fiber.
example :
    {g ∈ Fintype.piFinset (fun i => (univ : Finset (EmptyUnprescribedFiber i))) |
      ∀ i : {i // i ∈ ({true} : Finset Bool)}, g i.1 = prescribedUnit i}.card = 0 := by
  rw [Fintype.card_filter_piFinset_eqOn_of_mem (f := prescribedUnit) (hf := by simp)]
  rw [show (univ : Finset Bool) \ {true} = {false} by decide]
  simp [EmptyUnprescribedFiber]

private theorem filter_eqOn_restrict {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (S : Finset ι) (f : ι → κ) :
    (univ.filter fun g : ι → κ => ∀ i : {i // i ∈ S}, g i.1 = f i.1) =
      univ.filter fun g : ι → κ => ∀ i ∈ S, g i = f i := by
  ext g
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i.1 i.2

example {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι]
    [(i : ι) → DecidableEq (α i)] (s : (i : ι) → Finset (α i))
    (S : Finset ι) (f : (i : {i // i ∈ S}) → α i.1) (hf : ∀ i, f i ∈ s i.1) :
    {g ∈ Fintype.piFinset s | ∀ i, g i.1 = f i}.card =
      ∏ i ∈ univ \ S, (s i).card :=
  Fintype.card_filter_piFinset_eqOn_of_mem s S f hf

-- The general result specializes to Mathlib's existing one-coordinate API.
example {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι]
    [(i : ι) → DecidableEq (α i)] (s : (i : ι) → Finset (α i))
    (i : ι) (x : α i) (hx : x ∈ s i) :
    {g ∈ Fintype.piFinset s | g i = x}.card =
      ∏ j ∈ univ.erase i, (s j).card := by
  let f : (j : {j // j ∈ ({i} : Finset ι)}) → α j.1 := fun j => by
    have hji : j.1 = i := by simpa only [Finset.mem_singleton] using j.2
    rw [hji]
    exact x
  have h := Fintype.card_filter_piFinset_eqOn_of_mem s {i} f (by
      rintro ⟨j, hj⟩
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [f] using hx)
  have hfilter : {g ∈ Fintype.piFinset s | ∀ j, g j.1 = f j} =
      {g ∈ Fintype.piFinset s | g i = x} := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hg, heq⟩
      exact ⟨hg, by simpa [f] using heq ⟨i, by simp⟩⟩
    · rintro ⟨hg, heq⟩
      refine ⟨hg, fun j => ?_⟩
      have hj : j = ⟨i, by simp⟩ := Subtype.ext (by
        simpa only [Finset.mem_singleton] using j.2)
      subst j
      simpa [f] using heq
  rw [hfilter, Finset.sdiff_singleton_eq_erase] at h
  exact h

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : Finset ι) (f : {i // i ∈ S} → κ) :
    (univ.filter fun g : ι → κ => ∀ i, g i.1 = f i).card =
      Fintype.card κ ^ (Fintype.card ι - S.card) :=
  Fintype.card_filter_univ_eqOn S f

example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : Finset ι) (f : {i // i ∈ S} → κ) :
    (univ.filter fun g : ι → κ => ∀ i, g i.1 = f i).card *
      Fintype.card κ ^ S.card =
      Fintype.card κ ^ Fintype.card ι :=
  Fintype.card_filter_univ_eqOn_mul_pow_card S f

-- One prescribed coordinate leaves four of the eight functions `Fin 3 → Bool`.
example : (univ.filter fun g : Fin 3 → Bool =>
    ∀ i ∈ ({0} : Finset (Fin 3)), g i = true).card = 4 := by
  calc
    _ = (univ.filter fun g : Fin 3 → Bool =>
        ∀ i : {i // i ∈ ({0} : Finset (Fin 3))}, g i.1 = true).card :=
      congrArg Finset.card (filter_eqOn_restrict ({0} : Finset (Fin 3))
        (fun _ => true)).symm
    _ = _ := Fintype.card_filter_univ_eqOn _ _
    _ = 4 := by norm_num

-- Two coordinates receive different prescribed values.
example : (univ.filter fun g : Fin 3 → Bool => ∀ i ∈ ({0, 2} : Finset (Fin 3)),
    g i = if i = 0 then true else false).card = 2 := by
  calc
    _ = (univ.filter fun g : Fin 3 → Bool =>
        ∀ i : {i // i ∈ ({0, 2} : Finset (Fin 3))},
          g i.1 = if i.1 = 0 then true else false).card :=
      congrArg Finset.card (filter_eqOn_restrict ({0, 2} : Finset (Fin 3))
        (fun i => if i = 0 then true else false)).symm
    _ = _ := Fintype.card_filter_univ_eqOn _ _
    _ = 2 := by norm_num

-- Prescribing all four coordinates leaves one function.
example : (univ.filter fun g : Fin 4 → Bool => ∀ i ∈ (univ : Finset (Fin 4)),
    g i = decide (i.val % 2 = 0)).card = 1 := by
  calc
    _ = (univ.filter fun g : Fin 4 → Bool =>
        ∀ i : {i // i ∈ (univ : Finset (Fin 4))},
          g i.1 = decide (i.1.val % 2 = 0)).card :=
      congrArg Finset.card (filter_eqOn_restrict (univ : Finset (Fin 4))
        (fun i => decide (i.val % 2 = 0))).symm
    _ = _ := Fintype.card_filter_univ_eqOn _ _
    _ = 1 := by norm_num

-- Prescribing no coordinates leaves every function.
example : (univ.filter fun g : Fin 3 → Bool =>
    ∀ i ∈ (∅ : Finset (Fin 3)), g i = true).card = 8 := by
  calc
    _ = (univ.filter fun g : Fin 3 → Bool =>
        ∀ i : {i // i ∈ (∅ : Finset (Fin 3))}, g i.1 = true).card :=
      congrArg Finset.card (filter_eqOn_restrict (∅ : Finset (Fin 3))
        (fun _ => true)).symm
    _ = _ := Fintype.card_filter_univ_eqOn _ _
    _ = 8 := by norm_num

-- There is one function between empty types, and the multiplicative identity uses `0 ^ 0 = 1`.
example : (univ.filter fun g : Fin 0 → Fin 0 =>
    ∀ i ∈ (∅ : Finset (Fin 0)), g i = Fin.elim0 i).card = 1 := by
  calc
    _ = (univ.filter fun g : Fin 0 → Fin 0 =>
        ∀ i : {i // i ∈ (∅ : Finset (Fin 0))}, g i.1 = Fin.elim0 i.1).card :=
      congrArg Finset.card (filter_eqOn_restrict (∅ : Finset (Fin 0))
        (fun i => Fin.elim0 i)).symm
    _ = _ := Fintype.card_filter_univ_eqOn _ _
    _ = 1 := by norm_num

example : (univ.filter fun g : Fin 0 → Fin 0 =>
    ∀ i ∈ (∅ : Finset (Fin 0)), g i = Fin.elim0 i).card *
      Fintype.card (Fin 0) ^ (∅ : Finset (Fin 0)).card =
      Fintype.card (Fin 0) ^ Fintype.card (Fin 0) := by
  calc
    _ = (univ.filter fun g : Fin 0 → Fin 0 =>
        ∀ i : {i // i ∈ (∅ : Finset (Fin 0))}, g i.1 = Fin.elim0 i.1).card *
          Fintype.card (Fin 0) ^ (∅ : Finset (Fin 0)).card := by
      rw [congrArg Finset.card (filter_eqOn_restrict (∅ : Finset (Fin 0))
        (fun i => Fin.elim0 i))]
      simp
    _ = _ := Fintype.card_filter_univ_eqOn_mul_pow_card ∅ fun i => by
      rcases i with ⟨i, hi⟩
      simp at hi

-- No prescribed total function exists from a nonempty type to an empty one.
example : IsEmpty (Fin 1 → Fin 0) := ⟨fun f => Fin.elim0 (f 0)⟩

private def emptyPrescription
    (i : {i : Fin 1 // i ∈ (∅ : Finset (Fin 1))}) : Fin 0 := by
  rcases i with ⟨i, hi⟩
  simp at hi

-- An empty prescription exists even when no total function into the codomain exists.
example : (univ.filter fun g : Fin 1 → Fin 0 =>
    ∀ i : {i // i ∈ (∅ : Finset (Fin 1))}, g i.1 = emptyPrescription i).card = 0 := by
  rw [Fintype.card_filter_univ_eqOn]
  norm_num

-- The division-free identity retains `0 * 0 ^ 0 = 0 ^ 1` in that case.
example : (univ.filter fun g : Fin 1 → Fin 0 =>
    ∀ i : {i // i ∈ (∅ : Finset (Fin 1))}, g i.1 = emptyPrescription i).card *
      Fintype.card (Fin 0) ^ (∅ : Finset (Fin 1)).card =
      Fintype.card (Fin 0) ^ Fintype.card (Fin 1) :=
  Fintype.card_filter_univ_eqOn_mul_pow_card ∅ emptyPrescription

-- The source's one-coordinate statement is a direct client of the generic result.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (a : ι) (γ : κ) :
    (univ.filter fun g : ι → κ => g a = γ).card * Fintype.card κ =
      Fintype.card κ ^ Fintype.card ι := by
  have h := Fintype.card_filter_univ_eqOn_mul_pow_card ({a} : Finset ι) (fun _ => γ)
  rw [filter_eqOn_restrict ({a} : Finset ι) (fun _ => γ)] at h
  simpa using h

-- The source's two-coordinate statement permits different prescribed values.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {a b : ι} (hab : a ≠ b) (γ γ' : κ) :
    (univ.filter fun g : ι → κ => g a = γ ∧ g b = γ').card * Fintype.card κ ^ 2 =
      Fintype.card κ ^ Fintype.card ι := by
  have h := Fintype.card_filter_univ_eqOn_mul_pow_card ({a, b} : Finset ι)
    (fun i => if i.1 = a then γ else γ')
  rw [filter_eqOn_restrict ({a, b} : Finset ι) (fun i => if i = a then γ else γ')] at h
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
    (fun i => if i.1 = a ∨ i.1 = a' then γ else γ')
  rw [filter_eqOn_restrict ({a, b, a', b'} : Finset ι)
    (fun i => if i = a ∨ i = a' then γ else γ')] at h
  have hc : #({a, b, a', b'} : Finset ι) = 4 := by
    rw [card_insert_of_notMem (by simp [hab, h1, h2]),
      card_insert_of_notMem (by simp [h3, h4]), card_pair h5]
  rw [hc] at h
  simpa [hab.symm, h1.symm, h2.symm, h3, h3.symm, h4.symm, h5.symm, and_assoc] using h

#print axioms Fintype.card_filter_piFinset_eqOn_of_mem
#print axioms Fintype.card_filter_univ_eqOn
#print axioms Fintype.card_filter_univ_eqOn_mul_pow_card
