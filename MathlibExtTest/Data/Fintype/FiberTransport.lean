/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Data.Fintype.FiberTransport
import Mathlib.Tactic.NormNum

private def firstHalf (x : Fin 4) : ℕ := if x.val < 2 then 0 else 1

private def parity (x : Fin 4) : ℕ := x.val % 2

private theorem firstHalf_lt_two (x : Fin 4) : firstHalf x < 2 := by
  simp only [firstHalf]
  split <;> omega

private theorem parity_lt_two (x : Fin 4) : parity x < 2 := by
  exact Nat.mod_lt _ (by omega)

private theorem card_fiber_firstHalf_eq_parity (y : ℕ) :
    Fintype.card {x : Fin 4 // firstHalf x = y} =
      Fintype.card {x : Fin 4 // parity x = y} := by
  by_cases hy : y < 2
  · have : y = 0 ∨ y = 1 := by omega
    rcases this with rfl | rfl <;> decide
  · have hfirst := Fintype.card_eq_zero_iff.mpr
      ⟨fun (x : {x : Fin 4 // firstHalf x = y}) => hy (x.property ▸ firstHalf_lt_two x)⟩
    have hparity := Fintype.card_eq_zero_iff.mpr
      ⟨fun (x : {x : Fin 4 // parity x = y}) => hy (x.property ▸ parity_lt_two x)⟩
    exact hfirst.trans hparity.symm

private def fourNats : Finset ℕ := {0, 1, 2, 3}

private def twoNats : Finset ℕ := {0, 1}

private theorem modTwo_mapsTo : Set.MapsTo (fun n : ℕ => n % 2) fourNats twoNats := by
  intro n _
  simpa [twoNats] using Nat.mod_two_eq_zero_or_one n

private theorem modTwo_fibers_equal : ∀ x ∈ twoNats, ∀ x' ∈ twoNats,
    (fourNats.filter fun n => n % 2 = x).card ≤
      (fourNats.filter fun n => n % 2 = x').card := by
  intro x hx x' hx'
  simp only [twoNats, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> decide

-- Two classes of size two can be transported from consecutive halves to parity classes.
example : ∃ p : Equiv.Perm (Fin 4), ∀ x, parity (p x) = firstHalf x :=
  Fintype.exists_perm_of_fiber firstHalf parity card_fiber_firstHalf_eq_parity

-- A constant profile cannot be transported to the two-class profile.
example : ¬∃ p : Equiv.Perm (Fin 4), ∀ x,
    (fun _ : Fin 4 => (0 : ℕ)) (p x) = firstHalf x := by
  rintro ⟨p, hp⟩
  simpa [firstHalf] using hp 2

-- The empty profile has one permutation and no fiber-positivity requirement.
example : ∃ p : Equiv.Perm (Fin 0), ∀ x,
    (fun _ : Fin 0 => (3 : ℕ)) (p x) = (fun _ : Fin 0 => (3 : ℕ)) x := by
  exact Fintype.exists_perm_of_fiber (fun _ : Fin 0 => (3 : ℕ)) (fun _ => 3)
    (fun _ => rfl)

-- The singleton boundary transports its only label.
example : ∃ p : Equiv.Perm (Fin 1), ∀ x,
    (fun _ : Fin 1 => (7 : ℕ)) (p x) = (fun _ : Fin 1 => (7 : ℕ)) x := by
  exact Fintype.exists_perm_of_fiber (fun _ : Fin 1 => (7 : ℕ)) (fun _ => 7)
    (fun _ => rfl)

example {V C : Type*} [Fintype V] [DecidableEq C] (α β : V → C)
    (h : ∀ y, Fintype.card {x // α x = y} = Fintype.card {x // β x = y}) :
    ∃ p : Equiv.Perm V, ∀ x, β (p x) = α x :=
  Fintype.exists_perm_of_fiber α β h

-- The source's finite-filter formulation is an exact client of the subtype-cardinality API.
example {V C : Type*} [Fintype V] [DecidableEq C] (α β : V → C)
    (h : ∀ y, (Finset.univ.filter fun x => α x = y).card =
      (Finset.univ.filter fun x => β x = y).card) :
    ∃ p : Equiv.Perm V, ∀ x, β (p x) = α x := by
  apply Fintype.exists_perm_of_fiber α β
  intro y
  simpa only [Fintype.card_subtype] using h y

example {Ω X : Type*} [DecidableEq X] (Ωs : Finset Ω) (f : Ω → X)
    (Xs : Finset X) (hf : Set.MapsTo f Ωs Xs)
    (hconst : ∀ x ∈ Xs, ∀ x' ∈ Xs,
      (Ωs.filter fun e => f e = x).card ≤ (Ωs.filter fun e => f e = x').card)
    (Q : X → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : ((Xs.filter Q).card : ℝ) ≤ ε * Xs.card) :
    ((Ωs.filter fun e => Q (f e)).card : ℝ) ≤ ε * Ωs.card :=
  Finset.card_filter_le_of_fibers Ωs f Xs hf hconst Q ε hQ

-- The parity cover transfers the sharp density bound `2 ≤ 2` on infinite carriers.
example : ((fourNats.filter fun n => n % 2 = 1).card : ℝ) ≤
    (1 / 2 : ℝ) * fourNats.card := by
  exact Finset.card_filter_le_of_fibers fourNats (fun n : ℕ => n % 2) twoNats
    modTwo_mapsTo modTwo_fibers_equal (fun x => x = 1) (1 / 2) (by
      norm_num [twoNats, Finset.filter_insert, Finset.filter_singleton])

example : (fourNats.filter fun n => n % 2 = 1).card = 2 ∧
    (1 / 2 : ℝ) * fourNats.card = 2 := by
  norm_num [fourNats, Finset.filter_insert, Finset.filter_singleton]

-- Empty source and target carriers permit a negative coefficient because both sides vanish.
example : (((∅ : Finset ℕ).filter fun _ => True).card : ℝ) ≤
    (-1 : ℝ) * (∅ : Finset ℕ).card := by
  exact Finset.card_filter_le_of_fibers (∅ : Finset ℕ) id (∅ : Finset ℕ)
    (by simp) (by simp) (fun _ => True) (-1) (by norm_num)

-- A nonempty target carrier may consist entirely of zero fibers when the source carrier is empty.
example : (((∅ : Finset ℕ).filter fun _ => False).card : ℝ) ≤
    (0 : ℝ) * (∅ : Finset ℕ).card := by
  exact Finset.card_filter_le_of_fibers (∅ : Finset ℕ) id twoNats
    (by intro e he; simp at he) (by simp) (fun _ => False) 0 (by simp)

-- Without equal fibers, target density `1 / 2` can pull back to source density `1`.
example :
    (¬∀ x ∈ twoNats, ∀ x' ∈ twoNats,
      (fourNats.filter fun _ => (0 : ℕ) = x).card ≤
        (fourNats.filter fun _ => (0 : ℕ) = x').card) ∧
    (((twoNats.filter fun x => x = 0).card : ℝ) ≤ (1 / 2 : ℝ) * twoNats.card) ∧
    ¬(((fourNats.filter fun e => (fun _ : ℕ => 0) e = 0).card : ℝ) ≤
      (1 / 2 : ℝ) * fourNats.card) := by
  constructor
  · intro h
    have h01 := h 0 (by simp [twoNats]) 1 (by simp [twoNats])
    norm_num [fourNats, Finset.filter_insert, Finset.filter_singleton] at h01
  · constructor <;>
      norm_num [twoNats, fourNats, Finset.filter_insert, Finset.filter_singleton]

#print axioms Fintype.exists_perm_of_fiber
#print axioms Finset.card_filter_le_of_fibers
