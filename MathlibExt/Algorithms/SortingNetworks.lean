/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Bool.Basic

@[expose] public section


/-- A comparator on positions `i j` of an array `x : Fin n → α`:
put the smaller value at `i` and the larger at `j` (compare and
exchange). -/
noncomputable def comparator {n : ℕ} {α : Type*} [LinearOrder α]
    (i j : Fin n) (x : Fin n → α) : Fin n → α :=
  Function.update (Function.update x i (min (x i) (x j))) j
    (max (x i) (x j))

/-- A sorting network: a list of comparators applied in order. -/
noncomputable def Network.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : List (Fin n × Fin n)) (x : Fin n → α) : Fin n → α :=
  net.foldl (fun y c => comparator c.1 c.2 y) x

/-- An array is sorted if it is monotone. -/
def SortedArr {n : ℕ} {α : Type*} [Preorder α] (x : Fin n → α) :
    Prop := Monotone x

private theorem bool_min_eq_and : ∀ a b : Bool, min a b = (a && b) := by
  decide

private theorem bool_max_eq_or : ∀ a b : Bool, max a b = (a || b) := by
  decide

private theorem decide_le_min_eq {α : Type*} [LinearOrder α] (t a b : α) :
    decide (t ≤ min a b) = min (decide (t ≤ a)) (decide (t ≤ b)) := by
  rw [bool_min_eq_and (decide (t ≤ a)) (decide (t ≤ b))]
  by_cases ha : t ≤ a <;> by_cases hb : t ≤ b <;> simp [ha, hb]

private theorem decide_le_max_eq {α : Type*} [LinearOrder α] (t a b : α) :
    decide (t ≤ max a b) = max (decide (t ≤ a)) (decide (t ≤ b)) := by
  rw [bool_max_eq_or (decide (t ≤ a)) (decide (t ≤ b))]
  by_cases ha : t ≤ a <;> by_cases hb : t ≤ b <;> simp [le_max_iff, ha, hb]

private def theta {n : ℕ} {α : Type*} [LinearOrder α]
    (t : α) (x : Fin n → α) : Fin n → Bool :=
  fun i => decide (t ≤ x i)

private theorem theta_apply {n : ℕ} {α : Type*} [LinearOrder α]
    (t : α) (x : Fin n → α) (k : Fin n) :
    theta t x k = decide (t ≤ x k) := rfl

private theorem theta_comparator {n : ℕ} {α : Type*} [LinearOrder α]
    (t : α) (i j : Fin n) (y : Fin n → α) :
    theta t (comparator i j y) = comparator i j (theta t y) := by
  funext k
  simp only [theta_apply, comparator]
  by_cases hkj : k = j
  · rw [hkj, Function.update_self, Function.update_self]
    exact decide_le_max_eq t (y i) (y j)
  · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
    by_cases hki : k = i
    · rw [hki, Function.update_self, Function.update_self]
      exact decide_le_min_eq t (y i) (y j)
    · rw [Function.update_of_ne hki, Function.update_of_ne hki]
      exact (theta_apply t y k).symm

private theorem theta_exec {n : ℕ} {α : Type*} [LinearOrder α]
    (t : α) (net : List (Fin n × Fin n)) (y : Fin n → α) :
    theta t (Network.exec net y) = Network.exec net (theta t y) := by
  induction net generalizing y with
  | nil => rfl
  | cons c cs ih =>
      have h1 : Network.exec (c :: cs) y =
          Network.exec cs (comparator c.1 c.2 y) := rfl
      have h2 : Network.exec (c :: cs) (theta t y) =
          Network.exec cs (comparator c.1 c.2 (theta t y)) := rfl
      rw [h1, h2, ih, theta_comparator]

/-- The 0-1 principle: a comparator network that sorts every
Boolean input sorts every input over any linear order. -/
theorem zero_one_principle {n : ℕ} {α : Type*} [LinearOrder α]
    (net : List (Fin n × Fin n))
    (h01 : ∀ x : Fin n → Bool, SortedArr (Network.exec net x)) :
    ∀ x : Fin n → α, SortedArr (Network.exec net x) := by
  intro x
  show Monotone (Network.exec net x)
  intro i j hij
  by_contra hcon
  have hlt : Network.exec net x j < Network.exec net x i :=
    lt_of_not_ge hcon
  have hmono : Monotone (Network.exec net (theta (Network.exec net x i) x)) :=
    h01 (theta (Network.exec net x i) x)
  have hle := hmono hij
  rw [← theta_exec] at hle
  simp only [theta_apply] at hle
  have htrue : decide (Network.exec net x i ≤ Network.exec net x i) = true := by
    simp
  have hfalse : decide (Network.exec net x i ≤ Network.exec net x j) = false := by
    simp [not_le_of_gt hlt]
  rw [htrue, hfalse] at hle
  exact absurd hle (by decide)
