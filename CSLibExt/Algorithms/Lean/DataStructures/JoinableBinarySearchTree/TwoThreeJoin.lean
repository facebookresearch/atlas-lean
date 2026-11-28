/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic

/-!
# Joinable binary search trees: 2–3-tree join (Exercise 10.3)

Exercise 10.3 of Chapter 10: `join` for 2–3-trees. The Chapter 7
prerequisites `Tree23` / `height23` / `complete23` / `inorder23` /
`Upi23` / `treei` / `hi23`, the spine-descent `joinL23` / `joinR23`
returning `Upi23` with disjunctive specifications, and `join23` with
`complete_join23` / `inorder_join23` — exactly the two properties
Exercise 10.3 asks for.

## Provenance

Book Chapter 7 (2–3 trees) and Chapter 10, Exercise 10.3. There is no
Isabelle formalization of this exercise; the definitions follow the
book, with `joinL23` / `joinR23` following the red–black `joinL` /
`joinR` spine-descent idea plus the Chapter 7 insertion pattern.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u}

/-- 2-3-trees (book Ch. 7): a leaf, a 2-node `Node2 l a r` with one key
and two children, or a 3-node `Node3 l a m b r` with two keys and three
children. -/
public inductive Tree23 (α : Type u) where
  | Leaf : Tree23 α
  | Node2 : Tree23 α → α → Tree23 α → Tree23 α
  | Node3 : Tree23 α → α → Tree23 α → α → Tree23 α → Tree23 α
deriving DecidableEq

/-- Height of a 2-3-tree (book Ch. 7, `h`). -/
public def height23 : Tree23 α → ℕ
  | .Leaf => 0
  | .Node2 l _ r => max (height23 l) (height23 r) + 1
  | .Node3 l _ m _ r => max (height23 l) (max (height23 m) (height23 r)) + 1

/-- Completeness of a 2-3-tree (book Ch. 7, `complete`): all leaves at the
same depth. -/
public def complete23 : Tree23 α → Prop
  | .Leaf => True
  | .Node2 l _ r => height23 l = height23 r ∧ complete23 l ∧ complete23 r
  | .Node3 l _ m _ r =>
    height23 l = height23 m ∧ height23 m = height23 r ∧
      complete23 l ∧ complete23 m ∧ complete23 r

/-- Inorder traversal of a 2-3-tree (book Ch. 7, `inorder`). -/
public def inorder23 : Tree23 α → List α
  | .Leaf => []
  | .Node2 l a r => inorder23 l ++ a :: inorder23 r
  | .Node3 l a m b r => inorder23 l ++ a :: inorder23 m ++ b :: inorder23 r

/-- The `upi` type of Ch. 7: either a tree of the expected height (`Eqi`),
or two trees of the expected height with a separator key between them
(`Of`), meaning the tree grew by one level. -/
public inductive Upi23 (α : Type u) where
  | Eqi : Tree23 α → Upi23 α
  | Of : Tree23 α → α → Tree23 α → Upi23 α
deriving DecidableEq

/-- Collapse an `upi` (book Ch. 7, `treei`): `Of l a r` becomes `Node2 l a r`. -/
public def treei : Upi23 α → Tree23 α
  | .Eqi t => t
  | .Of l a r => .Node2 l a r

/-- Height of an `upi` (book Ch. 7, `hi`). -/
public def hi23 : Upi23 α → ℕ
  | .Eqi t => height23 t
  | .Of l _ _ => height23 l

/-- `joinL23`: join `l` (shorter or equal) to the left of `r`, descending
the left spine of `r` like `joinL` for red–black trees. The equal-height
step returns `Of l x r`: the join tree `Node2 l x r` has height
`height23 r + 1`, represented as an overflow. -/
public def joinL23 : Tree23 α → α → Tree23 α → Upi23 α
  | l, x, .Leaf => .Of l x .Leaf
  | l, x, .Node2 l' b r' =>
    if height23 l = height23 (.Node2 l' b r') then .Of l x (.Node2 l' b r')
    else match joinL23 l x l' with
      | .Eqi t => .Eqi (.Node2 t b r')
      | .Of t1 a t2 => .Eqi (.Node3 t1 a t2 b r')
  | l, x, .Node3 l' b m' c r' =>
    if height23 l = height23 (.Node3 l' b m' c r') then .Of l x (.Node3 l' b m' c r')
    else match joinL23 l x l' with
      | .Eqi t => .Eqi (.Node3 t b m' c r')
      | .Of t1 a t2 => .Of (.Node2 t1 a t2) b (.Node2 m' c r')

/-- `joinR23`: join `r` (shorter or equal) to the right of `l`, descending
the right spine of `l` (mirror of `joinL23`). -/
public def joinR23 : Tree23 α → α → Tree23 α → Upi23 α
  | .Leaf, x, r => .Of .Leaf x r
  | .Node2 l' b r', x, r =>
    if height23 r = height23 (.Node2 l' b r') then .Of (.Node2 l' b r') x r
    else match joinR23 r' x r with
      | .Eqi t => .Eqi (.Node2 l' b t)
      | .Of t1 a t2 => .Eqi (.Node3 l' b t1 a t2)
  | .Node3 l' b m' c r', x, r =>
    if height23 r = height23 (.Node3 l' b m' c r') then .Of (.Node3 l' b m' c r') x r
    else match joinR23 r' x r with
      | .Eqi t => .Eqi (.Node3 l' b m' c t)
      | .Of t1 a t2 => .Of (.Node2 l' b m') c (.Node2 t1 a t2)

/-- The `joinL23` specification (the "slightly more involved" properties
the book mentions): either a same-height tree with the joined inorder,
or an overflow pair of same-height trees whose `Node2` has the joined
inorder. -/
public theorem joinL23_spec (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 l ≤ height23 r) :
    (∃ t, joinL23 l x r = .Eqi t ∧ complete23 t ∧ height23 t = height23 r ∧
      inorder23 t = inorder23 l ++ x :: inorder23 r) ∨
    (∃ t1 a t2, joinL23 l x r = .Of t1 a t2 ∧ complete23 t1 ∧ complete23 t2 ∧
      height23 t1 = height23 r ∧ height23 t2 = height23 r ∧
      inorder23 t1 ++ a :: inorder23 t2 = inorder23 l ++ x :: inorder23 r) := by
  induction r generalizing l with
  | Leaf =>
    have h0 : height23 l = 0 := by simp only [height23] at hle; omega
    exact Or.inr ⟨l, x, .Leaf, rfl, hc_l, trivial, h0, rfl, rfl⟩
  | Node2 l' b r' ihl ihr =>
    have hc_l' : complete23 l' := hc_r.2.1
    have hc_r' : complete23 r' := hc_r.2.2
    have hheq : height23 l' = height23 r' := hc_r.1
    by_cases heq : height23 l = height23 (.Node2 l' b r')
    · exact Or.inr ⟨l, x, .Node2 l' b r', by simp [joinL23, heq], hc_l, hc_r, heq, rfl, rfl⟩
    · have hlt : height23 l < height23 (.Node2 l' b r') := by omega
      have hle' : height23 l ≤ height23 l' := by
        simp only [height23] at hlt; omega
      rcases ihl l hc_l hc_l' hle' with ⟨t, hrec, hct, hht, hin⟩ | ⟨t1, a, t2, hrec, hct1, hct2, hht1, hht2, hin⟩
      · refine Or.inl ⟨.Node2 t b r', by simp [joinL23, heq, hrec],
          ⟨by omega, hct, hc_r'⟩, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]
      · refine Or.inl ⟨.Node3 t1 a t2 b r', by simp [joinL23, heq, hrec],
          ⟨by omega, by omega, hct1, hct2, hc_r'⟩, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]
  | Node3 l' b m' c r' ihl ihm ihr =>
    have hc_l' : complete23 l' := hc_r.2.2.1
    have hc_m' : complete23 m' := hc_r.2.2.2.1
    have hc_r' : complete23 r' := hc_r.2.2.2.2
    have hheq1 : height23 l' = height23 m' := hc_r.1
    have hheq2 : height23 m' = height23 r' := hc_r.2.1
    by_cases heq : height23 l = height23 (.Node3 l' b m' c r')
    · exact Or.inr ⟨l, x, .Node3 l' b m' c r', by simp [joinL23, heq], hc_l, hc_r, heq, rfl, rfl⟩
    · have hlt : height23 l < height23 (.Node3 l' b m' c r') := by omega
      have hle' : height23 l ≤ height23 l' := by
        simp only [height23] at hlt; omega
      rcases ihl l hc_l hc_l' hle' with ⟨t, hrec, hct, hht, hin⟩ | ⟨t1, a, t2, hrec, hct1, hct2, hht1, hht2, hin⟩
      · refine Or.inl ⟨.Node3 t b m' c r', by simp [joinL23, heq, hrec],
          ⟨by omega, by omega, hct, hc_m', hc_r'⟩, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]
      · refine Or.inr ⟨.Node2 t1 a t2, b, .Node2 m' c r', by simp [joinL23, heq, hrec],
          ⟨by omega, hct1, hct2⟩, ⟨by omega, hc_m', hc_r'⟩, ?_, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]

/-- The `joinR23` specification (mirror of `joinL23_spec`). -/
public theorem joinR23_spec (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 r ≤ height23 l) :
    (∃ t, joinR23 l x r = .Eqi t ∧ complete23 t ∧ height23 t = height23 l ∧
      inorder23 t = inorder23 l ++ x :: inorder23 r) ∨
    (∃ t1 a t2, joinR23 l x r = .Of t1 a t2 ∧ complete23 t1 ∧ complete23 t2 ∧
      height23 t1 = height23 l ∧ height23 t2 = height23 l ∧
      inorder23 t1 ++ a :: inorder23 t2 = inorder23 l ++ x :: inorder23 r) := by
  induction l generalizing r with
  | Leaf =>
    have h0 : height23 r = 0 := by simp only [height23] at hle; omega
    exact Or.inr ⟨.Leaf, x, r, rfl, trivial, hc_r, rfl, h0, by simp [inorder23]⟩
  | Node2 l' b r' ihl ihr =>
    have hc_l' : complete23 l' := hc_l.2.1
    have hc_r' : complete23 r' := hc_l.2.2
    have hheq : height23 l' = height23 r' := hc_l.1
    by_cases heq : height23 r = height23 (.Node2 l' b r')
    · exact Or.inr ⟨.Node2 l' b r', x, r, by simp [joinR23, heq], hc_l, hc_r, rfl, heq, rfl⟩
    · have hlt : height23 r < height23 (.Node2 l' b r') := by omega
      have hle' : height23 r ≤ height23 r' := by
        simp only [height23] at hlt; omega
      rcases ihr r hc_r' hc_r hle' with ⟨t, hrec, hct, hht, hin⟩ | ⟨t1, a, t2, hrec, hct1, hct2, hht1, hht2, hin⟩
      · refine Or.inl ⟨.Node2 l' b t, by simp [joinR23, heq, hrec],
          ⟨by omega, hc_l', hct⟩, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]
      · refine Or.inl ⟨.Node3 l' b t1 a t2, by simp [joinR23, heq, hrec],
          ⟨by omega, by omega, hc_l', hct1, hct2⟩, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [inorder23]; simp [List.append_assoc, List.cons_append, hin]
  | Node3 l' b m' c r' ihl ihm ihr =>
    have hc_l' : complete23 l' := hc_l.2.2.1
    have hc_m' : complete23 m' := hc_l.2.2.2.1
    have hc_r' : complete23 r' := hc_l.2.2.2.2
    have hheq1 : height23 l' = height23 m' := hc_l.1
    have hheq2 : height23 m' = height23 r' := hc_l.2.1
    by_cases heq : height23 r = height23 (.Node3 l' b m' c r')
    · exact Or.inr ⟨.Node3 l' b m' c r', x, r, by simp [joinR23, heq], hc_l, hc_r, rfl, heq, rfl⟩
    · have hlt : height23 r < height23 (.Node3 l' b m' c r') := by omega
      have hle' : height23 r ≤ height23 r' := by
        simp only [height23] at hlt; omega
      rcases ihr r hc_r' hc_r hle' with ⟨t, hrec, hct, hht, hin⟩ | ⟨t1, a, t2, hrec, hct1, hct2, hht1, hht2, hin⟩
      · refine Or.inl ⟨.Node3 l' b m' c t, by simp [joinR23, heq, hrec],
          ⟨by omega, by omega, hc_l', hc_m', hct⟩, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]
      · refine Or.inr ⟨.Node2 l' b m', c, .Node2 t1 a t2, by simp [joinR23, heq, hrec],
          ⟨by omega, hc_l', hc_m'⟩, ⟨by omega, hct1, hct2⟩, ?_, ?_, ?_⟩
        · simp only [height23]; omega
        · simp only [height23]; omega
        · simp only [inorder23]; rw [hin]; simp [List.append_assoc, List.cons_append]

/-- `hi` of `joinL23`: the `upi` has the height of `r`. -/
public theorem hi23_joinL23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 l ≤ height23 r) :
    hi23 (joinL23 l x r) = height23 r := by
  rcases joinL23_spec l x r hc_l hc_r hle with ⟨t, hrec, _, hht, _⟩ | ⟨t1, _, _, hrec, _, _, hht1, _, _⟩
  · rw [hrec]; exact hht
  · rw [hrec]; exact hht1

/-- `treei` of `joinL23` is complete. -/
public theorem treei_complete_joinL23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 l ≤ height23 r) :
    complete23 (treei (joinL23 l x r)) := by
  rcases joinL23_spec l x r hc_l hc_r hle with ⟨t, hrec, hct, _, _⟩ | ⟨t1, _, t2, hrec, hct1, hct2, hht1, hht2, _⟩
  · rw [hrec]; exact hct
  · rw [hrec]; exact ⟨by omega, hct1, hct2⟩

/-- `treei` of `joinL23` has the joined inorder. -/
public theorem inorder_treei_joinL23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 l ≤ height23 r) :
    inorder23 (treei (joinL23 l x r)) = inorder23 l ++ x :: inorder23 r := by
  rcases joinL23_spec l x r hc_l hc_r hle with ⟨t, hrec, _, _, hin⟩ | ⟨t1, a, t2, hrec, _, _, _, _, hin⟩
  · rw [hrec]; exact hin
  · rw [hrec]; exact hin

/-- `hi` of `joinR23`: the `upi` has the height of `l`. -/
public theorem hi23_joinR23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 r ≤ height23 l) :
    hi23 (joinR23 l x r) = height23 l := by
  rcases joinR23_spec l x r hc_l hc_r hle with ⟨t, hrec, _, hht, _⟩ | ⟨t1, _, _, hrec, _, _, hht1, _, _⟩
  · rw [hrec]; exact hht
  · rw [hrec]; exact hht1

/-- `treei` of `joinR23` is complete. -/
public theorem treei_complete_joinR23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 r ≤ height23 l) :
    complete23 (treei (joinR23 l x r)) := by
  rcases joinR23_spec l x r hc_l hc_r hle with ⟨t, hrec, hct, _, _⟩ | ⟨t1, _, t2, hrec, hct1, hct2, hht1, hht2, _⟩
  · rw [hrec]; exact hct
  · rw [hrec]; exact ⟨by omega, hct1, hct2⟩

/-- `treei` of `joinR23` has the joined inorder. -/
public theorem inorder_treei_joinR23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) (hle : height23 r ≤ height23 l) :
    inorder23 (treei (joinR23 l x r)) = inorder23 l ++ x :: inorder23 r := by
  rcases joinR23_spec l x r hc_l hc_r hle with ⟨t, hrec, _, _, hin⟩ | ⟨t1, a, t2, hrec, _, _, _, _, hin⟩
  · rw [hrec]; exact hin
  · rw [hrec]; exact hin

/-- The overall 2-3-tree `join` (Ex. 10.3): descend into the taller side,
or build a `Node2` at equal heights. Following the general idea of the
`join` function for red–black trees, `joinL23` / `joinR23` return a
`Upi23`, which `treei` turns into a tree. The stated properties are
`complete23` and `inorder23` only (`complete_join23`, `inorder_join23`;
the book does not ask for `bst` here). -/
public def join23 : Tree23 α → α → Tree23 α → Tree23 α
  | l, x, r =>
    if height23 l > height23 r then treei (joinR23 l x r)
    else if height23 l < height23 r then treei (joinL23 l x r)
    else .Node2 l x r

/-- `join23` preserves completeness (Ex. 10.3, first property). -/
public theorem complete_join23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) : complete23 (join23 l x r) := by
  simp only [join23]
  by_cases h1 : height23 l > height23 r
  · rw [ite_eq_left h1]
    exact treei_complete_joinR23 l x r hc_l hc_r (by omega)
  · rw [ite_eq_right h1]
    by_cases h2 : height23 l < height23 r
    · rw [ite_eq_left h2]
      exact treei_complete_joinL23 l x r hc_l hc_r (by omega)
    · rw [ite_eq_right h2]
      exact ⟨by omega, hc_l, hc_r⟩

/-- `join23` has the joined inorder (Ex. 10.3, second property). -/
public theorem inorder_join23 (l : Tree23 α) (x : α) (r : Tree23 α)
    (hc_l : complete23 l) (hc_r : complete23 r) :
    inorder23 (join23 l x r) = inorder23 l ++ x :: inorder23 r := by
  simp only [join23]
  by_cases h1 : height23 l > height23 r
  · rw [ite_eq_left h1]
    exact inorder_treei_joinR23 l x r hc_l hc_r (by omega)
  · rw [ite_eq_right h1]
    by_cases h2 : height23 l < height23 r
    · rw [ite_eq_left h2]
      exact inorder_treei_joinL23 l x r hc_l hc_r (by omega)
    · rw [ite_eq_right h2]
      rfl

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
