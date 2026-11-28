/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Balancing a list into a Braun tree (`bal`)

`bal` (Chapter 4, §4.3.1), its specification (`bal_spec`, Lemma 4.9's
content plus Braunness), `bal_braun` (Exercise 11.4),
`bal_acomplete` (Corollary 4.12), the `bal_list` / `balance_list` /
`bal_tree` / `balance_tree` wrappers, and the linear running time of
`bal` (`Tbal`, `Tbal_le`, Exercise 4.9).

## Cost model

`Tbal` counts one unit per call and matches on `bal`'s result, as
the book's recurrence does: a call with parameter `n + 1` spawns
calls at `(n+1)/2` and `n - (n+1)/2`, whose parameters sum to `n`.
The counter measures calls of this function, not allocation,
traversal, or total runtime.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theory (`Balance.thy`).
The book is Tobias Nipkow (ed.), *Functional Data Structures and
Algorithms* (ACM Books, 2025; text version of July 27, 2026),
Chapter 4, §4.3.1, and Chapter 11, Exercise 11.4.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `bal n xs` (Chapter 4, §4.3.1). Both recursive calls decrease `n`
(`(n+1)/2 < n+1` and `n - (n+1)/2 < n+1`), so `omega` discharges both
decreasing goals. -/
def bal : ℕ → List α → Tree α × List α
  | 0, xs => (.Leaf, xs)
  | n + 1, xs =>
    match bal ((n + 1) / 2) xs with
    | (l, []) => (l, [])
    | (l, y :: ys') =>
      match bal (n - (n + 1) / 2) ys' with
      | (r, zs) => (.Node l y r, zs)
  termination_by n _ => n
  decreasing_by all_goals omega

/-- **Lemma 4.9** (Chapter 4, strengthened with Braunness for Exercise 11.4):
`n ≤ |xs| ∧ bal n xs = (t, zs)` implies `braun t`, `inorder t = take n xs`,
`zs = drop n xs`, and `|t| = n`. Proved by induction on `n`. In the step,
the two recursive calls give Braun trees `l`, `r` with `|l| = (n+1)/2`
and `|r| = n - (n+1)/2`; the size disjunction for `braun ⟨l; y; r⟩` is the
parity of `n + 1` (even: `|l| = |r| + 1`; odd: `|l| = |r|`). -/
theorem bal_spec {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) :
    braun t ∧ inorder t = List.take n xs ∧ zs = List.drop n xs ∧ size t = n := by
  induction n using Nat.strong_induction_on generalizing xs t zs with
  | _ n ih =>
    cases n with
    | zero =>
      simp only [bal] at h
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
      exact ⟨braun_leaf, rfl, rfl, rfl⟩
    | succ n' =>
      have hbal : bal (n' + 1) xs =
          match bal ((n' + 1) / 2) xs with
          | (l, []) => (l, [])
          | (l, y :: ys') =>
            match bal (n' - (n' + 1) / 2) ys' with
            | (r, zs) => (.Node l y r, zs) := by
        simp only [bal]
      rw [hbal] at h
      cases h1 : bal ((n' + 1) / 2) xs with
      | mk l ys =>
        cases ys with
        | nil =>
          rw [h1] at h
          dsimp only at h
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
          exfalso
          have hIH := ih ((n' + 1) / 2) (by omega) (xs := xs) (t := l) (zs := [])
            (by omega) h1
          have hlen : xs.length ≤ (n' + 1) / 2 := by
            have hlen' := congrArg List.length hIH.2.2.1
            simp only [List.length_nil, List.length_drop] at hlen'
            omega
          omega
        | cons y ys' =>
          rw [h1] at h
          dsimp only at h
          cases h2 : bal (n' - (n' + 1) / 2) ys' with
          | mk r zs' =>
            rw [h2] at h
            dsimp only at h
            obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
            have hIH1 := ih ((n' + 1) / 2) (by omega) (xs := xs) (t := l)
              (zs := y :: ys') (by omega) h1
            obtain ⟨hbl, hinl, hdrop1, hszl⟩ := hIH1
            have hlen_l : (inorder l).length = (n' + 1) / 2 := by
              rw [inorder_length, hszl]
            have hm' : n' - (n' + 1) / 2 ≤ ys'.length := by
              have hlen1 : (y :: ys').length
                  = (List.drop ((n' + 1) / 2) xs).length := by
                rw [← hdrop1]
              simp only [List.length_cons, List.length_drop] at hlen1
              omega
            have hIH2 := ih (n' - (n' + 1) / 2) (by omega) (xs := ys') (t := r)
              (zs := zs') hm' h2
            obtain ⟨hbr, hinr, hdrop2, hszr⟩ := hIH2
            have hbraun : braun (Tree.Node l y r) := by
              rw [braun_node]
              refine ⟨?_, hbl, hbr⟩
              rw [hszl, hszr]
              by_cases hev : (n' + 1) % 2 = 0
              · right; omega
              · left; omega
            have hxs : xs = inorder l ++ (y :: ys') := by
              rw [hinl, hdrop1, List.take_append_drop]
            have htake : List.take (n' + 1) xs = inorder l ++ (y :: inorder r) := by
              rw [hxs, List.take_append]
              have htake1 : List.take (n' + 1) (inorder l) = inorder l :=
                List.take_of_length_le (by rw [hlen_l]; omega)
              rw [htake1, show n' + 1 - (inorder l).length
                  = n' - (n' + 1) / 2 + 1 from by rw [hlen_l]; omega,
                List.take_succ_cons, ← hinr]
            have hdrop : List.drop (n' + 1) xs = zs' := by
              rw [hxs, List.drop_append]
              have hdrop1 : List.drop (n' + 1) (inorder l) = [] := by
                apply List.eq_nil_of_length_eq_zero
                rw [List.length_drop, hlen_l]
                omega
              rw [hdrop1, List.nil_append, show n' + 1 - (inorder l).length
                  = n' - (n' + 1) / 2 + 1 from by rw [hlen_l]; omega,
                List.drop_succ_cons]
              exact hdrop2.symm
            refine ⟨hbraun, ?_, ?_, ?_⟩
            · exact (rfl : inorder (Tree.Node l y r)
                = inorder l ++ (y :: inorder r)).trans htake.symm
            · exact hdrop.symm
            · simp only [size_node, hszl, hszr]; omega

/-- **Exercise 11.4.** `bal` in §4.3.1 produces Braun trees:
`n ≤ |xs| ∧ bal n xs = (t, zs) ⟹ braun t`. -/
theorem bal_braun {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) : braun t :=
  (bal_spec hn h).1

/-- **Corollary 4.12** (Chapter 4): `bal` returns an almost-complete tree. -/
theorem bal_acomplete {n : ℕ} {xs : List α} (hn : n ≤ xs.length)
    {t : Tree α} {zs : List α} (h : bal n xs = (t, zs)) : acomplete t :=
  braun_acomplete (bal_braun hn h)

/-- `bal_list n xs = fst (bal n xs)` (Chapter 4): the tree built from the
first `n` elements of `xs`. -/
def bal_list (n : ℕ) (xs : List α) : Tree α := (bal n xs).1

/-- `balance_list xs = bal_list |xs| xs` (Chapter 4). -/
def balance_list (xs : List α) : Tree α := bal_list xs.length xs

/-- `inorder (bal_list n xs) = take n xs`. -/
theorem bal_list_inorder {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    inorder (bal_list n xs) = List.take n xs := by
  show inorder ((bal n xs).1) = List.take n xs
  cases h : bal n xs with
  | mk t zs =>
    show inorder t = List.take n xs
    exact (bal_spec hn h).2.1

/-- `braun (bal_list n xs)`. -/
theorem bal_list_braun {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    braun (bal_list n xs) := by
  show braun ((bal n xs).1)
  cases h : bal n xs with
  | mk t zs =>
    show braun t
    exact (bal_spec hn h).1

/-- `inorder (balance_list xs) = xs`. -/
theorem balance_list_inorder {xs : List α} :
    inorder (balance_list xs) = xs := by
  show inorder (bal_list xs.length xs) = xs
  rw [bal_list_inorder (le_refl _), List.take_of_length_le (le_refl _)]

/-- `braun (balance_list xs)`. -/
theorem balance_list_braun {xs : List α} : braun (balance_list xs) := by
  show braun (bal_list xs.length xs)
  exact bal_list_braun (le_refl _)

/-- `bal_tree n t = bal_list n (inorder t)` (Chapter 4). -/
def bal_tree (n : ℕ) (t : Tree α) : Tree α := bal_list n (inorder t)

/-- `balance_tree t = bal_tree |t| t` (Chapter 4). -/
def balance_tree (t : Tree α) : Tree α := bal_tree (size t) t

/-- `inorder (bal_tree n t) = take n (inorder t)`. -/
theorem bal_tree_inorder {n : ℕ} {t : Tree α} (hn : n ≤ size t) :
    inorder (bal_tree n t) = List.take n (inorder t) := by
  show inorder (bal_list n (inorder t)) = List.take n (inorder t)
  exact bal_list_inorder (by rwa [inorder_length])

/-- `inorder (balance_tree t) = inorder t`. -/
theorem balance_tree_inorder {t : Tree α} :
    inorder (balance_tree t) = inorder t := by
  show inorder (bal_tree (size t) t) = inorder t
  rw [bal_tree_inorder (le_refl _),
    List.take_of_length_le (by simp [inorder_length])]

/-- `Tbal n xs`: running time of `bal n xs` (Exercise 4.9): 1 per call. -/
def Tbal : ℕ → List α → ℕ
  | 0, _ => 1
  | n + 1, xs =>
    match bal ((n + 1) / 2) xs with
    | (l, []) => 1 + Tbal ((n + 1) / 2) xs
    | (l, y :: ys') => 1 + Tbal ((n + 1) / 2) xs + Tbal (n - (n + 1) / 2) ys'
  termination_by n _ => n
  decreasing_by all_goals omega

/-- **Exercise 4.9.** `bal` runs in linear time in its first argument:
`Tbal n xs ≤ 4 * n + 1`. (The constant 4 counts calls: each call with
parameter `n + 1` spawns calls at `(n+1)/2` and `n - (n+1)/2`, whose
parameters sum to `n`.) -/
theorem Tbal_le (n : ℕ) (xs : List α) : Tbal n xs ≤ 4 * n + 1 := by
  induction n using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    cases n with
    | zero => simp [Tbal]
    | succ n' =>
      have hT : Tbal (n' + 1) xs =
          match bal ((n' + 1) / 2) xs with
          | (l, []) => 1 + Tbal ((n' + 1) / 2) xs
          | (l, y :: ys') =>
            1 + Tbal ((n' + 1) / 2) xs + Tbal (n' - (n' + 1) / 2) ys' := by
        simp only [Tbal]
      rw [hT]
      cases h1 : bal ((n' + 1) / 2) xs with
      | mk l ys =>
        cases ys with
        | nil =>
          dsimp only
          have hih := ih ((n' + 1) / 2) (by omega) (xs := xs)
          have hm : (n' + 1) / 2 ≤ n' := by omega
          calc 1 + Tbal ((n' + 1) / 2) xs
              ≤ 1 + (4 * ((n' + 1) / 2) + 1) := Nat.add_le_add_left hih 1
            _ ≤ 4 * (n' + 1) + 1 := by omega
        | cons y ys' =>
          dsimp only
          have hih1 := ih ((n' + 1) / 2) (by omega) (xs := xs)
          have hih2 := ih (n' - (n' + 1) / 2) (by omega) (xs := ys')
          have hdiv : (n' + 1) / 2 + (n' - (n' + 1) / 2) = n' := by omega
          calc 1 + Tbal ((n' + 1) / 2) xs + Tbal (n' - (n' + 1) / 2) ys'
              ≤ 1 + (4 * ((n' + 1) / 2) + 1) + (4 * (n' - (n' + 1) / 2) + 1) :=
                Nat.add_le_add (Nat.add_le_add_left hih1 1) hih2
            _ ≤ 4 * (n' + 1) + 1 := by omega

end BraunTree
end Cslib.Algorithms.Lean
