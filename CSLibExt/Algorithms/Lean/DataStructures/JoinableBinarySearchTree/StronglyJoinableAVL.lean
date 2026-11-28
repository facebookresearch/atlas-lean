/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Joinable_BST_Work_Bounds/StronglyJoinableAVL.thy` (Archive of Formal Proofs, entry
`Joinable_BST_Work_Bounds`, https://www.isa-afp.org/entries/Joinable_BST_Work_Bounds.html):
Copyright (c) 2004, Gerwin Klein, Tobias Nipkow, Lawrence C. Paulson
Copyright (c) 2004, contributing authors (see author notice in individual files)
All rights reserved.
Licensed under the BSD License of the Archive of Formal Proofs (https://isa-afp.org/LICENSE).
Authors: Marco Haucke
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.StronglyJoinable
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.AvlJoin
public import Mathlib.Tactic

/-!
# Joinable binary search trees: AVL strongly joinable instance

The AVL instance of the strongly joinable framework: the rank is
`height`, with `avl_rule_bal` / `avl_rule_mono` / `avl_rule_sub`, the
timing functions `TavlJoinR` / `TavlJoinL` / `TavlJoin` with their
bounds and the cost rule `avl_rule_cost`, node counts for `balL` /
`balR` / `avlJoinR` / `avlJoinL` / `avlJoin`, and the
`StronglyJoinableData` instance `avlStronglyJoinable`.

## Provenance

`StronglyJoinableAVL.thy` in the AFP entry `Joinable_BST_Work_Bounds`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u} [LinearOrder α]

/-- Every AVL tree satisfies the balancing rule (AFP `rule_bal` for AVL). -/
public theorem avl_rule_bal (t : Tree α Nat) (h : avl t) :
    balancedOf (fun t => (height t : ℝ)) 1 2 t := by
  induction t with
  | Leaf => trivial
  | Node l kv r ihl ihr =>
    obtain ⟨a, n⟩ := kv
    have hbal : ((height l : ℤ) - (height r : ℤ)).natAbs ≤ 1 := h.1
    have hle1 : height l ≤ height r + 1 := by omega
    have hle2 : height r ≤ height l + 1 := by omega
    have hn : height (Tree.Node l (a, n) r) = max (height l) (height r) + 1 := rfl
    have hN : max (height l) (height r) + 1 ≤ min (height l) (height r) + 2 := by omega
    show max ((height l : ℝ)) ((height r : ℝ)) + 1 ≤ (height (Tree.Node l (a, n) r) : ℝ) ∧
      (height (Tree.Node l (a, n) r) : ℝ) ≤ min ((height l : ℝ)) ((height r : ℝ)) + 2 ∧
      balancedOf (fun t => (height t : ℝ)) 1 2 l ∧ balancedOf (fun t => (height t : ℝ)) 1 2 r
    refine ⟨by rw [hn]; exact_mod_cast le_refl _, by rw [hn]; exact_mod_cast hN,
      ihl h.2.2.1, ihr h.2.2.2⟩

/-- Monotonicity rule for the AVL rank (AFP `rule_mono` for AVL). -/
public theorem avl_rule_mono {l r : Tree α Nat} {a : α} (hl : avl l) (hr : avl r) :
    max ((height l : ℝ)) ((height r : ℝ)) ≤ (height (avlJoin l a r) : ℝ) := by
  rcases join_height l a r hl hr with h | h
  · rw [h]
    push_cast
    exact le_refl _
  · rw [h]
    push_cast
    linarith

/-- Submodularity rule for the AVL rank (AFP `rule_sub` for AVL). -/
public theorem avl_rule_sub {l' l r' r : Tree α Nat} {a : α} {b : Nat} {x : ℝ}
    (h1 : (height l' : ℝ) ≤ (height l : ℝ) + x) (h2 : (height r' : ℝ) ≤ (height r : ℝ) + x)
    (hl' : avl l') (hr' : avl r') :
    (height (avlJoin l' a r') : ℝ) ≤ (height (Tree.Node l (a, b) r) : ℝ) + x := by
  have hub : (height (avlJoin l' a r') : ℝ) ≤ max ((height l' : ℝ)) ((height r' : ℝ)) + 1 := by
    rcases join_height l' a r' hl' hr' with h | h
    · rw [h]
      push_cast
      linarith
    · rw [h]
      push_cast
      exact le_refl _
  have hmax : max ((height l' : ℝ)) ((height r' : ℝ)) ≤ max ((height l : ℝ)) ((height r : ℝ)) + x := by
    apply max_le
    · calc (height l' : ℝ) ≤ (height l : ℝ) + x := h1
        _ ≤ max ((height l : ℝ)) ((height r : ℝ)) + x := by
            exact add_le_add (le_max_left _ _) (le_refl x)
    · calc (height r' : ℝ) ≤ (height r : ℝ) + x := h2
        _ ≤ max ((height l : ℝ)) ((height r : ℝ)) + x := by
            exact add_le_add (le_max_right _ _) (le_refl x)
  have hchild : max ((height l : ℝ)) ((height r : ℝ)) + 1 ≤
      (height (Tree.Node l (a, b) r) : ℝ) := by
    have hn : height (Tree.Node l (a, b) r) = max (height l) (height r) + 1 := rfl
    rw [hn]
    push_cast
    exact le_refl _
  linarith

/-- Timing function for `avlJoinR` (AFP `T_joinR` for AVL): every
invocation, the stopping one included, costs one, as AFP's `time_fun`
charges every call; `ht` / `node` / `balR` cost 0. -/
public def TavlJoinR : Tree α Nat → α → Tree α Nat → ℕ
  | .Leaf, _, _ => 1
  | .Node _ _ r', a, r => if ht r' ≤ ht r + 1 then 1 else TavlJoinR r' a r + 1

/-- Timing function for `avlJoinL` (AFP `T_joinL` for AVL, mirror of
`TavlJoinR`): every invocation, the stopping one included, costs one. -/
public def TavlJoinL : Tree α Nat → α → Tree α Nat → ℕ
  | _, _, .Leaf => 1
  | l, a, .Node l' _ _ => if ht l' ≤ ht l + 1 then 1 else TavlJoinL l a l' + 1

/-- Timing function for `avlJoin` (AFP `T_join` for AVL): the
equal-height case costs 0. -/
public def TavlJoin (l : Tree α Nat) (a : α) (r : Tree α Nat) : ℕ :=
  if ht l > ht r + 1 then TavlJoinR l a r
  else if ht r > ht l + 1 then TavlJoinL l a r
  else 0

/-- Bound for `TavlJoinR` (AFP `T_joinR` for AVL). -/
public theorem TavlJoinR_bound (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hl : avl l) (hr : avl r) (hgt : ht l > ht r + 1) :
    TavlJoinR l a r ≤ 1 + (height l - height r) := by
  induction l with
  | Leaf =>
    have h0 : ht (Tree.Leaf : Tree α Nat) = 0 := rfl
    omega
  | Node l' kv r' ihl ihr =>
    obtain ⟨k', n'⟩ := kv
    by_cases hc : ht r' ≤ ht r + 1
    · have hT : TavlJoinR (Tree.Node l' (k', n') r') a r = 1 := by
        simp only [TavlJoinR, ite_eq_left hc]
      rw [hT]
      omega
    · have hT : TavlJoinR (Tree.Node l' (k', n') r') a r = TavlJoinR r' a r + 1 := by
        simp only [TavlJoinR, ite_eq_right hc]
      rw [hT]
      have hIH := ihr hl.2.2.2 (by omega : ht r' > ht r + 1)
      have htr' : ht r' = height r' := ht_height r' hl.2.2.2
      have htr : ht r = height r := ht_height r hr
      have hheight : height (Tree.Node l' (k', n') r') = max (height l') (height r') + 1 := rfl
      rw [hheight]
      omega

/-- Bound for `TavlJoinL` (AFP `T_joinL` for AVL). -/
public theorem TavlJoinL_bound (l : Tree α Nat) (a : α) (r : Tree α Nat)
    (hl : avl l) (hr : avl r) (hgt : ht r > ht l + 1) :
    TavlJoinL l a r ≤ 1 + (height r - height l) := by
  induction r with
  | Leaf =>
    have h0 : ht (Tree.Leaf : Tree α Nat) = 0 := rfl
    omega
  | Node l' kv r' ihl ihr =>
    obtain ⟨k', n'⟩ := kv
    by_cases hc : ht l' ≤ ht l + 1
    · have hT : TavlJoinL l a (Tree.Node l' (k', n') r') = 1 := by
        simp only [TavlJoinL, ite_eq_left hc]
      rw [hT]
      omega
    · have hT : TavlJoinL l a (Tree.Node l' (k', n') r') = TavlJoinL l a l' + 1 := by
        simp only [TavlJoinL, ite_eq_right hc]
      rw [hT]
      have hIH := ihl hr.2.2.1 (by omega : ht l' > ht l + 1)
      have htl' : ht l' = height l' := ht_height l' hr.2.2.1
      have htl : ht l = height l := ht_height l hl
      have hheight : height (Tree.Node l' (k', n') r') = max (height l') (height r') + 1 := rfl
      rw [hheight]
      omega

/-- The cost rule for AVL (AFP `rule_cost` for AVL). -/
public theorem avl_rule_cost (l r : Tree α Nat) (a : α) (hl : avl l) (hr : avl r) :
    (TavlJoin l a r : ℝ) ≤ 1 + |(height l : ℝ) - (height r : ℝ)| := by
  rcases lt_trichotomy (ht r) (ht l) with h1 | h1 | h1
  · by_cases h2 : ht l > ht r + 1
    · have hT : TavlJoin l a r = TavlJoinR l a r := by simp [TavlJoin, h2]
      rw [hT]
      have hB := TavlJoinR_bound l a r hl hr h2
      have hht : ht l = height l := ht_height l hl
      have hhtr : ht r = height r := ht_height r hr
      have hle : height r ≤ height l := by omega
      have hleR : (height r : ℝ) ≤ (height l : ℝ) := by exact_mod_cast hle
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (height l : ℝ) - (height r : ℝ))]
      have hB2 : (TavlJoinR l a r : ℝ) ≤ 1 + ((height l - height r : ℕ) : ℝ) := by
        exact_mod_cast hB
      rw [Nat.cast_sub hle] at hB2
      linarith
    · have hT : TavlJoin l a r = 0 := by
        simp [TavlJoin, h2, show ¬ ht r > ht l + 1 by omega]
      rw [hT]
      push_cast
      have habs := abs_nonneg ((height l : ℝ) - (height r : ℝ))
      linarith
  · have hT : TavlJoin l a r = 0 := by
      simp [TavlJoin, show ¬ ht l > ht r + 1 by omega, show ¬ ht r > ht l + 1 by omega]
    rw [hT]
    push_cast
    have habs := abs_nonneg ((height l : ℝ) - (height r : ℝ))
    linarith
  · by_cases h2 : ht r > ht l + 1
    · have hT : TavlJoin l a r = TavlJoinL l a r := by
        simp [TavlJoin, show ¬ ht l > ht r + 1 by omega, h2]
      rw [hT]
      have hB := TavlJoinL_bound l a r hl hr h2
      have hht : ht l = height l := ht_height l hl
      have hhtr : ht r = height r := ht_height r hr
      have hle : height l ≤ height r := by omega
      have hleR : (height l : ℝ) ≤ (height r : ℝ) := by exact_mod_cast hle
      rw [abs_of_nonpos (by linarith : (height l : ℝ) - (height r : ℝ) ≤ 0)]
      have hB2 : (TavlJoinL l a r : ℝ) ≤ 1 + ((height r - height l : ℕ) : ℝ) := by
        exact_mod_cast hB
      rw [Nat.cast_sub hle] at hB2
      linarith
    · have hT : TavlJoin l a r = 0 := by
        simp [TavlJoin, show ¬ ht l > ht r + 1 by omega, h2]
      rw [hT]
      push_cast
      have habs := abs_nonneg ((height l : ℝ) - (height r : ℝ))
      linarith

/-- Node count for `balL` (AFP `balL_size`). -/
public theorem tsize_balL (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    tsize (balL l a r) = tsize l + tsize r + 1 := by
  fun_cases balL l a r <;> simp only [tsize, node] <;> omega

/-- Node count for `balR` (AFP `balR_size`). -/
public theorem tsize_balR (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    tsize (balR l a r) = tsize l + tsize r + 1 := by
  fun_cases balR l a r <;> simp only [tsize, node] <;> omega

/-- Node count for `avlJoinR` (AFP `joinR_size`). -/
public theorem tsize_avlJoinR (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    tsize (avlJoinR l a r) = tsize l + tsize r + 1 := by
  induction l with
  | Leaf => rfl
  | Node l' kv r' ihl ihr =>
    obtain ⟨k', n'⟩ := kv
    have hNode : tsize (Tree.Node l' (k', n') r') = tsize l' + tsize r' + 1 := rfl
    have hn : tsize (node r' a r) = tsize r' + tsize r + 1 := rfl
    by_cases hc : ht r' ≤ ht r + 1
    · have h1 : avlJoinR (Tree.Node l' (k', n') r') a r = balR l' k' (node r' a r) := by
        simp only [avlJoinR, ite_eq_left hc]
      rw [h1, tsize_balR]
      omega
    · have h1 : avlJoinR (Tree.Node l' (k', n') r') a r = balR l' k' (avlJoinR r' a r) := by
        simp only [avlJoinR, ite_eq_right hc]
      rw [h1, tsize_balR, ihr]
      omega

/-- Node count for `avlJoinL` (AFP `joinL_size`). -/
public theorem tsize_avlJoinL (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    tsize (avlJoinL l a r) = tsize l + tsize r + 1 := by
  induction r with
  | Leaf => rfl
  | Node l' kv r' ihl ihr =>
    obtain ⟨k', n'⟩ := kv
    have hNode : tsize (Tree.Node l' (k', n') r') = tsize l' + tsize r' + 1 := rfl
    have hn : tsize (node l a l') = tsize l + tsize l' + 1 := rfl
    by_cases hc : ht l' ≤ ht l + 1
    · have h1 : avlJoinL l a (Tree.Node l' (k', n') r') = balL (node l a l') k' r' := by
        simp only [avlJoinL, ite_eq_left hc]
      rw [h1, tsize_balL]
      omega
    · have h1 : avlJoinL l a (Tree.Node l' (k', n') r') = balL (avlJoinL l a l') k' r' := by
        simp only [avlJoinL, ite_eq_right hc]
      rw [h1, tsize_balL, ihl]
      omega

/-- Node count for `avlJoin` (AFP `join_size` for AVL). -/
public theorem tsize_avlJoin (l : Tree α Nat) (a : α) (r : Tree α Nat) :
    tsize (avlJoin l a r) = tsize l + tsize r + 1 := by
  by_cases h1 : ht l > ht r + 1
  · have hjoin : avlJoin l a r = avlJoinR l a r := by simp [avlJoin, h1]
    rw [hjoin, tsize_avlJoinR]
  · by_cases h2 : ht r > ht l + 1
    · have hjoin : avlJoin l a r = avlJoinL l a r := by simp [avlJoin, h1, h2]
      rw [hjoin, tsize_avlJoinL]
    · have hjoin : avlJoin l a r = node l a r := by simp [avlJoin, h1, h2]
      rw [hjoin]
      rfl

/-- The AVL `StronglyJoinableData` instance (`StronglyJoinable`, `tree_ht`). -/
public def avlStronglyJoinable : StronglyJoinableData α Nat where
  toJoinData := avlJoinData
  rank := fun t => (height t : ℝ)
  c_l := 1
  c_u := 2
  c_vals := ⟨by norm_num, by norm_num, by norm_num⟩
  rank_leaf := by simp [height]
  inv_balanced := fun t h => avl_rule_bal t h
  T_join := TavlJoin
  k₀ := 1
  k₁ := 1
  rule_mono := by
    intro l r a hl hr
    exact avl_rule_mono hl hr
  rule_sub := by
    intro l' l r' r a b x h1 h2 hl' hr' _hnode
    exact avl_rule_sub h1 h2 hl' hr'
  join_size := by
    intro l r a hl hr
    exact tsize_avlJoin l a r
  rule_cost := by
    intro l r a hl hr
    rw [one_mul]
    exact avl_rule_cost l r a hl hr
  k₀_nonneg := by norm_num
  k₁_nonneg := by norm_num

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
