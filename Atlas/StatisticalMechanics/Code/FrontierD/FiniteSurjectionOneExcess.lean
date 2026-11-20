/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Combinatorics.Pigeonhole



open Finset

namespace StatMech.FrontierD




theorem finiteSurjection_fiber_eq_pair_of_card_eq_add_one
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Surjective f)
    (hcard : Fintype.card A = Fintype.card B + 1)
    {a b : A} (hab : a ≠ b) (hfab : f a = f b) :
    ∀ x : A, f x = f a → x = a ∨ x = b := by
  classical
  intro x hfx
  by_contra hx
  push_neg at hx
  let fiber (y : B) : Finset A :=
    Finset.univ.filter fun z => f z = y
  have hone (y : B) : 1 ≤ (fiber y).card := by
    obtain ⟨z, hz⟩ := hf y
    exact Finset.card_pos.mpr ⟨z, by simp [fiber, hz]⟩
  have hthree : 3 ≤ (fiber (f a)).card := by
    have hsub : ({a, b, x} : Finset A) ⊆ fiber (f a) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simp [fiber]
      · simp [fiber, hfab]
      · simp [fiber, hfx]
    have hcardThree : ({a, b, x} : Finset A).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
      · simp
      · simpa [Finset.mem_singleton] using hx.2.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hx.1.symm⟩
    rw [← hcardThree]
    exact Finset.card_le_card hsub
  have hsum : Fintype.card A =
      ∑ y : B, (fiber y).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A))
      (t := (Finset.univ : Finset B)) (f := f)
      (by intro z hz; exact Finset.mem_univ _)
    simpa [fiber] using h
  let rest := (Finset.univ : Finset B).erase (f a)
  have hrest : rest.card ≤ ∑ y ∈ rest, (fiber y).card := by
    calc
      rest.card = ∑ _y ∈ rest, 1 := by simp
      _ ≤ ∑ y ∈ rest, (fiber y).card := by
        apply Finset.sum_le_sum
        intro y hy
        exact hone y
  have htargetMem : f a ∈ (Finset.univ : Finset B) :=
    Finset.mem_univ _
  have hsplit :
      (∑ y : B, (fiber y).card) =
        (∑ y ∈ rest, (fiber y).card) + (fiber (f a)).card := by
    dsimp [rest]
    exact (Finset.sum_erase_add _ _ htargetMem).symm
  have hrestCard : rest.card + 1 = Fintype.card B := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem htargetMem, Finset.card_univ]
    omega
  have hlarge : Fintype.card B + 2 ≤ Fintype.card A := by
    rw [hsum, hsplit, ← hrestCard]
    omega
  omega



theorem finiteSurjection_fiber_eq_singleton_away_of_card_eq_add_one
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Surjective f)
    (hcard : Fintype.card A = Fintype.card B + 1)
    {a b : A} (hab : a ≠ b) (hfab : f a = f b)
    {x : A} (hxaway : f x ≠ f a) :
    ∀ y : A, f y = f x → y = x := by
  classical
  intro y hfy
  by_contra hyx
  let fiber (z : B) : Finset A :=
    Finset.univ.filter fun u => f u = z
  have hone (z : B) : 1 ≤ (fiber z).card := by
    obtain ⟨u, hu⟩ := hf z
    exact Finset.card_pos.mpr ⟨u, by simp [fiber, hu]⟩
  have htwo0 : 2 ≤ (fiber (f a)).card := by
    have hsub : ({a, b} : Finset A) ⊆ fiber (f a) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp [fiber]
      · simp [fiber, hfab]
    have hc : ({a, b} : Finset A).card = 2 := by simp [hab]
    rw [← hc]
    exact Finset.card_le_card hsub
  have htwo1 : 2 ≤ (fiber (f x)).card := by
    have hsub : ({x, y} : Finset A) ⊆ fiber (f x) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp [fiber]
      · simp [fiber, hfy]
    have hc : ({x, y} : Finset A).card = 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · simpa [Finset.mem_singleton] using Ne.symm hyx
    rw [← hc]
    exact Finset.card_le_card hsub
  have hsum : Fintype.card A = ∑ z : B, (fiber z).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A))
      (t := (Finset.univ : Finset B)) (f := f)
      (by intro z hz; exact Finset.mem_univ _)
    simpa [fiber] using h
  let rest := ((Finset.univ : Finset B).erase (f a)).erase (f x)
  have hrest : rest.card ≤ ∑ z ∈ rest, (fiber z).card := by
    calc
      rest.card = ∑ _z ∈ rest, 1 := by simp
      _ ≤ ∑ z ∈ rest, (fiber z).card := by
        apply Finset.sum_le_sum
        intro z hz
        exact hone z
  have hmem0 : f a ∈ (Finset.univ : Finset B) := Finset.mem_univ _
  have hmem1 : f x ∈ (Finset.univ : Finset B).erase (f a) := by
    simp [hxaway]
  have hBtwo : 2 ≤ Fintype.card B := by
    have hsub : ({f a, f x} : Finset B) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hc : ({f a, f x} : Finset B).card = 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · simpa [Finset.mem_singleton] using hxaway.symm
    rw [← hc]
    simpa only [Finset.card_univ] using Finset.card_le_card hsub
  have hrestCard : rest.card + 2 = Fintype.card B := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hmem1,
      Finset.card_erase_of_mem hmem0, Finset.card_univ]
    omega
  have hsplit :
      (∑ z : B, (fiber z).card) =
        (∑ z ∈ rest, (fiber z).card) +
          (fiber (f x)).card + (fiber (f a)).card := by
    calc
      (∑ z : B, (fiber z).card) =
          (∑ z ∈ (Finset.univ : Finset B).erase (f a),
            (fiber z).card) + (fiber (f a)).card :=
        (Finset.sum_erase_add _ _ hmem0).symm
      _ = ((∑ z ∈ rest, (fiber z).card) +
          (fiber (f x)).card) + (fiber (f a)).card := by
        rw [show (∑ z ∈ (Finset.univ : Finset B).erase (f a),
            (fiber z).card) =
              (∑ z ∈ rest, (fiber z).card) +
                (fiber (f x)).card by
          dsimp [rest]
          exact (Finset.sum_erase_add _ _ hmem1).symm]
  have hlarge : Fintype.card B + 2 ≤ Fintype.card A := by
    rw [hsum, hsplit, ← hrestCard]
    omega
  omega

end StatMech.FrontierD
