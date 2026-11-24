/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Testing.TestAdequacy
import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union

/-! # Deterministic sized generators

Finite-depth enumeration in the style of Runciman, Naylor and Lindblad,
SmallCheck and Lazy SmallCheck (Haskell 2008). The general interface is
parameterized by an abstract size function; the sorted-list example uses
constructor depth for natural-number lists. -/

@[expose] public section

namespace Cslib.Testing

/-- A deterministic sized enumerator: at bound `n`, the finite set `G n`. -/
abbrev SizedEnumerator (α : Type*) := ℕ → Finset α

/-- Every enumerated value satisfies `p`. -/
def SizedEnumerator.Sound {α : Type*} (G : SizedEnumerator α) (p : α → Prop) : Prop :=
  ∀ n x, x ∈ G n → p x

/-- Every `p`-input of size at most `n` is enumerated at bound `n`. -/
def SizedEnumerator.CompleteUpTo {α : Type*} (G : SizedEnumerator α)
    (size : α → ℕ) (p : α → Prop) : Prop :=
  ∀ n x, size x ≤ n → p x → x ∈ G n

/-- Bounded exhaustive coverage: passing `G n` covers all bounded `p`-inputs. -/
theorem enum_complete_bounded {D O : Type*} {G : SizedEnumerator D}
    {size : D → ℕ} {p : D → Prop}
    (hG : SizedEnumerator.CompleteUpTo G size p) (P : D → O)
    (S : D → O → Prop) (n : ℕ) (hpass : Passes P S (G n)) :
    ∀ x, size x ≤ n → p x → S x (P x) := by
  intro x hx hp
  exact hpass x (hG n x hx hp)

/-- Constructor depth of a natural-number list. -/
def natListDepth : List ℕ → ℕ
  | [] => 0
  | x :: xs => 1 + max x (natListDepth xs)

/-- All natural-number lists of constructor depth at most `n`, recursively. -/
def natLists : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 =>
      insert [] ((Finset.range (n + 1)).biUnion fun x =>
        (natLists n).image fun xs => x :: xs)

/-- The sorted natural-number lists of constructor depth at most `n`. -/
def sortedNatLists (n : ℕ) : Finset (List ℕ) :=
  (natLists n).filter fun xs => xs.Pairwise (· ≤ ·)

theorem mem_natLists_iff {xs : List ℕ} {n : ℕ} :
    xs ∈ natLists n ↔ natListDepth xs ≤ n := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [natLists, natListDepth]
      | cons x xs =>
          constructor
          · intro h
            simp only [natLists, Finset.mem_singleton] at h
            simp at h
          · intro h
            simp only [natListDepth] at h
            omega
  | succ n ih =>
      cases xs with
      | nil => simp [natLists, natListDepth]
      | cons x xs =>
          simp only [natLists, Finset.mem_insert, List.cons_ne_nil, false_or,
            Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨y, hyn, zs, hzs, hcon⟩
            simp only [List.cons.injEq] at hcon
            obtain ⟨hy, hz⟩ := hcon
            have hx : x ≤ n := by omega
            have hd : natListDepth xs ≤ n := by
              rw [← hz]
              exact ih.mp hzs
            simp only [natListDepth]
            omega
          · intro h
            simp only [natListDepth] at h
            exact ⟨x, by omega, xs, ih.mpr (by omega), rfl⟩

theorem mem_sortedNatLists_iff {xs : List ℕ} {n : ℕ} :
    xs ∈ sortedNatLists n ↔ xs.Pairwise (· ≤ ·) ∧ natListDepth xs ≤ n := by
  simp only [sortedNatLists, Finset.mem_filter, mem_natLists_iff]
  exact and_comm

theorem sortedNatLists_sound :
    SizedEnumerator.Sound sortedNatLists
      (fun xs : List ℕ => xs.Pairwise (· ≤ ·)) := by
  intro n x hx
  exact (mem_sortedNatLists_iff.mp hx).1

theorem sortedNatLists_completeUpTo :
    SizedEnumerator.CompleteUpTo sortedNatLists natListDepth
      (fun xs : List ℕ => xs.Pairwise (· ≤ ·)) := by
  intro n x hx hp
  exact mem_sortedNatLists_iff.mpr ⟨hp, hx⟩

end Cslib.Testing
