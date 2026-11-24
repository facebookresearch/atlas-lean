/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Splice
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Array
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.MinMax
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Fast size, and initialising a Braun tree

`diff` / `size_fast` (Lemma 11.3), `braun2_of` / `braun_of`
(initialising a Braun tree with a fixed value), `braun_of_naive`
(Exercise 11.7), and the running time of `size_fast`
(`Tdiff` / `Tsize_fast`, Exercise 11.8).

## Cost model

`Tdiff` counts one unit per call and descends along a single path
(`Tdiff_le_height`). `Tsize_fast` counts one unit plus `Tsize_fast r`
plus `Tdiff l (size_fast r)`. `Tsize_fast` is quadratic in the
height (`size_fast_time_le`). The counters measure calls of these
functions, not allocation, traversal, or total runtime.

## Provenance

A Lean formalisation of the Chapter 11 Isabelle development in the
Isabelle distribution's `HOL-Data_Structures` theory
(`Braun_Tree.thy`). The book is Tobias Nipkow (ed.), *Functional
Data Structures and Algorithms* (ACM Books, 2025; text version of
July 27, 2026), Chapter 11, §11.5.1, §11.5.2, and Exercises 11.7–11.8.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `diff t n`: for a Braun tree `t` with `|t| ∈ {n, n + 1}`, this is
`|t| - n`. It descends along one path (the book's definition). -/
def diff : Tree α → ℕ → ℕ
  | .Leaf, _ => 0
  | .Node l _ r, n =>
      if n = 0 then 1
      else if n % 2 = 0 then diff r (n / 2 - 1)
      else diff l (n / 2)

/-- `size_fast t`: the size of a Braun tree, computed in time quadratic
in the height (book §11.5.1). -/
def size_fast : Tree α → ℕ
  | .Leaf => 0
  | .Node l _ r => 1 + 2 * size_fast r + diff l (size_fast r)

/-- The `diff` correctness lemma (book §11.5.1). -/
theorem diff_spec {t : Tree α} (n : ℕ) (h : braun t)
    (hs : size t = n ∨ size t = n + 1) : diff t n = size t - n := by
  induction t generalizing n with
  | Leaf =>
    rcases hs with hs | hs
    · have h0 : size (Tree.Leaf : Tree α) = 0 := rfl
      have hn0 : n = 0 := by omega
      subst hn0; rfl
    · have h0 : size (Tree.Leaf : Tree α) = 0 := rfl; omega
  | Node l x r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    have hsize : size (Tree.Node l x r) = size l + size r + 1 := rfl
    by_cases hn0 : n = 0
    · subst hn0
      have h1 : size (Tree.Node l x r) = 1 := by omega
      simp [diff, h1]
    · by_cases hpar : n % 2 = 0
      · have hsr : size r = n / 2 - 1 ∨ size r = n / 2 := by omega
        have hsl : size l = n / 2 := by omega
        have hdiff := ihr (n / 2 - 1) hbr (by
          rcases hsr with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by omega))
        have e : diff (Tree.Node l x r) n = diff r (n / 2 - 1) := by
          simp [diff, hn0, hpar]
        rw [e, hdiff]
        omega
      · have hsl : size l = n / 2 ∨ size l = n / 2 + 1 := by omega
        have hsr : size r = n / 2 := by omega
        have hdiff := ihl (n / 2) hbl hsl
        have e : diff (Tree.Node l x r) n = diff l (n / 2) := by
          simp [diff, hn0, hpar]
        rw [e, hdiff]
        omega

/-- **Lemma 11.3.** `braun t ⟹ size_fast t = |t|`. -/
theorem size_fast_correct {t : Tree α} (h : braun t) : size_fast t = size t := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    obtain ⟨hsz, hbl, hbr⟩ := braun_node.mp h
    have h1 := ihr hbr
    have h2 := diff_spec (t := l) (n := size r) hbl hsz
    show 1 + 2 * size_fast r + diff l (size_fast r) = size l + size r + 1
    rw [h1, h2]
    omega

/-- `braun2_of x n`: the pair of Braun trees with `n` and `n + 1` copies
of `x`, built in parallel (book §11.5.2). Halving the index at each step
makes it logarithmic time. -/
def braun2_of : α → ℕ → Tree α × Tree α
  | x, n =>
      if n = 0 then (.Leaf, .Node .Leaf x .Leaf)
      else if n % 2 = 1 then
        let (t, u) := braun2_of x ((n - 1) / 2)
        (.Node t x t, .Node u x t)
      else
        let (t, u) := braun2_of x (n / 2 - 1)
        (.Node u x t, .Node u x u)
termination_by _x n => n
decreasing_by
  · have _h1 : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  · have h1 : n / 2 ≤ n := Nat.div_le_self n 2
    omega

/-- `braun2_of` correctness (the book's "more general statements":
`braun2_of_replicate` and `braun2_of_size_braun`). -/
theorem braun2_of_spec (x : α) (n : ℕ) :
    size (braun2_of x n).1 = n ∧ size (braun2_of x n).2 = n + 1 ∧
    braun (braun2_of x n).1 ∧ braun (braun2_of x n).2 ∧
    list (braun2_of x n).1 = List.replicate n x ∧
    list (braun2_of x n).2 = List.replicate (n + 1) x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [braun2_of, list, braun_node, splice, braun]
    · by_cases hpar : n % 2 = 1
      · have hm : (n - 1) / 2 < n := by omega
        obtain ⟨hs1, hs2, hb1, hb2, hl1, hl2⟩ := ih ((n - 1) / 2) hm
        have e : braun2_of x n
            = (.Node (braun2_of x ((n - 1) / 2)).1 x (braun2_of x ((n - 1) / 2)).1,
               .Node (braun2_of x ((n - 1) / 2)).2 x (braun2_of x ((n - 1) / 2)).1) := by
          conv_lhs => rw [braun2_of.eq_1, ite_eq_right hn0, ite_eq_left hpar]
        rw [e]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show size (Tree.Node (braun2_of x ((n - 1) / 2)).1 x
              (braun2_of x ((n - 1) / 2)).1) = n
          simp only [size_node]; omega
        · show size (Tree.Node (braun2_of x ((n - 1) / 2)).2 x
              (braun2_of x ((n - 1) / 2)).1) = n + 1
          simp only [size_node]; omega
        · show braun (Tree.Node (braun2_of x ((n - 1) / 2)).1 x
              (braun2_of x ((n - 1) / 2)).1)
          exact braun_node.mpr ⟨Or.inl rfl, hb1, hb1⟩
        · show braun (Tree.Node (braun2_of x ((n - 1) / 2)).2 x
              (braun2_of x ((n - 1) / 2)).1)
          exact braun_node.mpr ⟨Or.inr (by omega), hb2, hb1⟩
        · show x :: splice (list (braun2_of x ((n - 1) / 2)).1)
              (list (braun2_of x ((n - 1) / 2)).1) = List.replicate n x
          rw [hl1, splice_replicate]
          conv_rhs => rw [show n = (n - 1) + 1 from by omega, List.replicate_succ]
          have hAB : (n - 1) / 2 + (n - 1) / 2 = n - 1 := by omega
          rw [hAB]
        · show x :: splice (list (braun2_of x ((n - 1) / 2)).2)
              (list (braun2_of x ((n - 1) / 2)).1) = List.replicate (n + 1) x
          rw [hl2, hl1, splice_replicate]
          conv_rhs => rw [List.replicate_succ]
          have hAB : (n - 1) / 2 + 1 + (n - 1) / 2 = n := by omega
          rw [hAB]
      · have hne : n % 2 ≠ 1 := hpar
        have hm : n / 2 - 1 < n := by omega
        obtain ⟨hs1, hs2, hb1, hb2, hl1, hl2⟩ := ih (n / 2 - 1) hm
        have e : braun2_of x n
            = (.Node (braun2_of x (n / 2 - 1)).2 x (braun2_of x (n / 2 - 1)).1,
               .Node (braun2_of x (n / 2 - 1)).2 x (braun2_of x (n / 2 - 1)).2) := by
          conv_lhs => rw [braun2_of.eq_1, ite_eq_right hn0, ite_eq_right hne]
        rw [e]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show size (Tree.Node (braun2_of x (n / 2 - 1)).2 x
              (braun2_of x (n / 2 - 1)).1) = n
          simp only [size_node]; omega
        · show size (Tree.Node (braun2_of x (n / 2 - 1)).2 x
              (braun2_of x (n / 2 - 1)).2) = n + 1
          simp only [size_node]; omega
        · show braun (Tree.Node (braun2_of x (n / 2 - 1)).2 x
              (braun2_of x (n / 2 - 1)).1)
          exact braun_node.mpr ⟨Or.inr (by omega), hb2, hb1⟩
        · show braun (Tree.Node (braun2_of x (n / 2 - 1)).2 x
              (braun2_of x (n / 2 - 1)).2)
          exact braun_node.mpr ⟨Or.inl rfl, hb2, hb2⟩
        · show x :: splice (list (braun2_of x (n / 2 - 1)).2)
              (list (braun2_of x (n / 2 - 1)).1) = List.replicate n x
          rw [hl2, hl1, splice_replicate]
          conv_rhs => rw [show n = (n - 1) + 1 from by omega, List.replicate_succ]
          have hAB : n / 2 - 1 + 1 + (n / 2 - 1) = n - 1 := by omega
          rw [hAB]
        · show x :: splice (list (braun2_of x (n / 2 - 1)).2)
              (list (braun2_of x (n / 2 - 1)).2) = List.replicate (n + 1) x
          rw [hl2, splice_replicate]
          conv_rhs => rw [List.replicate_succ]
          have hAB : n / 2 - 1 + 1 + (n / 2 - 1 + 1) = n := by omega
          rw [hAB]

/-- `braun_of x n`: the Braun tree with `n` copies of `x`. -/
def braun_of (x : α) (n : ℕ) : Tree α := (braun2_of x n).1

/-- `list (braun_of x n) = replicate n x`. -/
theorem braun_of_list (x : α) (n : ℕ) : list (braun_of x n) = List.replicate n x :=
  (braun2_of_spec x n).2.2.2.2.1

/-- `braun (braun_of x n)`. -/
theorem braun_of_braun (x : α) (n : ℕ) : braun (braun_of x n) :=
  (braun2_of_spec x n).2.2.1

/-- `size (braun_of x n) = n`. -/
theorem braun_of_size (x : α) (n : ℕ) : size (braun_of x n) = n :=
  (braun2_of_spec x n).1

/-- **Exercise 11.7.** `braun_of_naive`: the naive O(n lg n) version of
`braun_of` (book §11.5.2). -/
def braun_of_naive : α → ℕ → Tree α
  | _, 0 => .Leaf
  | x, n + 1 =>
    if n % 2 = 0 then .Node (braun_of_naive x (n / 2)) x (braun_of_naive x (n / 2))
    else .Node (braun_of_naive x (n / 2 + 1)) x (braun_of_naive x (n / 2))
termination_by _ n => n
decreasing_by
  all_goals
    (by_cases hpos : 0 < n
     · have hd : n / 2 < n := Nat.div_lt_self (k := 2) hpos (by norm_num)
       have _hd1 : n / 2 - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) hd
       have _hd2 : n / 2 < n.succ := lt_of_le_of_lt (Nat.div_le_self n 2) (Nat.lt_succ_self n)
       have _hd3 : n / 2 + 1 < n.succ := Nat.succ_lt_succ hd
       assumption
     · push Not at hpos
       have h0 : n = 0 := by omega
       subst h0
       simp_all)

/-- **Exercise 11.7.** `list (braun_of_naive x n) = replicate n x`. -/
theorem braun_of_naive_list (x : α) (n : ℕ) :
    list (braun_of_naive x n) = List.replicate n x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [braun_of_naive, list]
    | succ n' =>
      rw [braun_of_naive]
      by_cases hpar : n' % 2 = 0
      · rw [ite_eq_left hpar]
        simp only [list]
        rw [ih (n' / 2) (by omega), splice_replicate]
        have hnn : n' / 2 + n' / 2 = n' := by omega
        rw [hnn, List.replicate_succ]
      · rw [ite_eq_right hpar]
        simp only [list]
        rw [ih (n' / 2 + 1) (by omega), ih (n' / 2) (by omega), splice_replicate]
        have hnn : n' / 2 + 1 + n' / 2 = n' := by omega
        rw [hnn, List.replicate_succ]

/-- **Exercise 11.8.** `Tdiff`: running time of `diff` (0 in the base cases). -/
def Tdiff : Tree α → ℕ → ℕ
  | .Leaf, _ => 0
  | .Node l _ r, n =>
    if n = 0 then 0
    else if n % 2 = 0 then 1 + Tdiff r (n / 2 - 1)
    else 1 + Tdiff l (n / 2)
termination_by _ n => n
decreasing_by
  all_goals
    (by_cases hpos : 0 < n
     · have hd : n / 2 < n := Nat.div_lt_self (k := 2) hpos (by norm_num)
       have _hd1 : n / 2 - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) hd
       have _hd2 : n / 2 < n.succ := lt_of_le_of_lt (Nat.div_le_self n 2) (Nat.lt_succ_self n)
       have _hd3 : n / 2 + 1 < n.succ := Nat.succ_lt_succ hd
       assumption
     · push Not at hpos
       have h0 : n = 0 := by omega
       subst h0
       simp_all)

/-- `Tdiff t n ≤ height t`: `diff` descends along one path. -/
theorem Tdiff_le_height (t : Tree α) (n : ℕ) : Tdiff t n ≤ height t := by
  induction n using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    cases t with
    | Leaf => simp [Tdiff]
    | Node l x r =>
      by_cases hn0 : n = 0
      · subst hn0; simp [Tdiff]
      · by_cases hpar : n % 2 = 0
        · have h1 : Tdiff (.Node l x r) n = 1 + Tdiff r (n / 2 - 1) := by
            simp [Tdiff, hn0, hpar]
          rw [h1]
          have hih := ih (n / 2 - 1) (by omega) r
          have he : height (.Node l x r) = max (height l) (height r) + 1 := rfl
          have hle : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
          omega
        · have h1 : Tdiff (.Node l x r) n = 1 + Tdiff l (n / 2) := by
            simp [Tdiff, hn0, hpar]
          rw [h1]
          have hih := ih (n / 2) (by omega) l
          have he : height (.Node l x r) = max (height l) (height r) + 1 := rfl
          have hle : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
          omega

/-- **Exercise 11.8.** `Tsize_fast`: running time of `size_fast`. -/
def Tsize_fast : Tree α → ℕ
  | .Leaf => 0
  | .Node l _ r => 1 + Tsize_fast r + Tdiff l (size_fast r)

/-- **Exercise 11.8.** `Tsize_fast` is quadratic in the height. -/
theorem size_fast_time_le (t : Tree α) : Tsize_fast t ≤ (height t) ^ 2 := by
  induction t with
  | Leaf => rfl
  | Node l x r ihl ihr =>
    show 1 + Tsize_fast r + Tdiff l (size_fast r) ≤ (height (.Node l x r)) ^ 2
    have hd := Tdiff_le_height l (size_fast r)
    have he : height (.Node l x r) = max (height l) (height r) + 1 := rfl
    rcases le_total (height l) (height r) with hle | hle
    · rw [Nat.max_eq_right hle] at he
      calc 1 + Tsize_fast r + Tdiff l (size_fast r)
          ≤ 1 + (height r) ^ 2 + height r := by omega
        _ ≤ (height r + 1) ^ 2 := by
          have hsq : (height r + 1) ^ 2
              = (height r) ^ 2 + 2 * height r + 1 := by ring
          omega
        _ = (height (.Node l x r)) ^ 2 := by rw [he]
    · rw [Nat.max_eq_left hle] at he
      have hpow : (height r) ^ 2 ≤ (height l) ^ 2 := Nat.pow_le_pow_left hle 2
      calc 1 + Tsize_fast r + Tdiff l (size_fast r)
          ≤ 1 + (height l) ^ 2 + height l := by omega
        _ ≤ (height l + 1) ^ 2 := by
          have hsq : (height l + 1) ^ 2
              = (height l) ^ 2 + 2 * height l + 1 := by ring
          omega
        _ = (height (.Node l x r)) ^ 2 := by rw [he]

end BraunTree
end Cslib.Algorithms.Lean
