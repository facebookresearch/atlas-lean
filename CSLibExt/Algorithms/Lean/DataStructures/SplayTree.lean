/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree

/-!
# Splay trees

Self-adjusting binary search trees (Sleator-Tarjan), following Demaine's
MIT 6.851 Lecture 5. The carrier is Mathlib's `BinaryTree`, reusing
`BinarySearchTree.inorder`, `BinarySearchTree.All`,
`BinarySearchTree.Ordered` and structural membership from
`BinarySearchTree`.

`splay x t` is the bottom-up splay: search for `x` as in a binary search
tree, then rotate the found node (or the last node visited) to the root
with the three double-rotation cases: zig (single rotation at the root),
zig-zig (rotate the grandparent-parent edge first), and zig-zag (rotate
the parent-node edge first). The definition pattern-matches two levels
of the tree at once, recursing into the relevant grandchild. `insert`
splays the key and then splits, `access` splays and reports whether the
key reached the root, and `contains` is its Boolean projection.

The module proves functional correctness only: splaying preserves the
inorder traversal (hence membership and `Ordered`), and a present key
ends at the root. The amortized `O(log n)` access lemma (the
Sleator-Tarjan potential argument) is out of scope.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace SplayTree

open BinarySearchTree

@[simp] private theorem mem_nil {α : Type u} {x : α} :
    x ∈ (BinaryTree.nil : BinaryTree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node {α : Type u} {x key : α}
    {left right : BinaryTree α} :
    x ∈ BinaryTree.node key left right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/-- The key at the root of a tree, if any. -/
public def root? {α : Type u} : BinaryTree α → Option α
  | .nil => none
  | .node key _ _ => some key

@[simp] public theorem root?_nil {α : Type u} :
    root? (.nil : BinaryTree α) = none :=
  rfl

@[simp] public theorem root?_node {α : Type u} {key : α}
    {left right : BinaryTree α} :
    root? (.node key left right) = some key :=
  rfl

/--
Splay `x` to the root. The search descends as in a binary search tree;
the restructuring pattern-matches the child on the search path, so each
recursive step performs a zig (single rotation), a zig-zig (both
rotations in the same direction, grandparent edge first), or a zig-zag
(rotations in opposite directions, parent edge first). When `x` is
absent, the node where the search stops is what the rotations carry
upward; branches where the splayed grandchild is empty fall back to a
single zig that carries that last visited node one level up.
-/
public def splay {α : Type u} [LinearOrder α] (x : α) :
    BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node k l r =>
      if x = k then .node k l r
      else if x < k then
        match l with
        | .nil => .node k l r
        | .node lk ll lr =>
            if x = lk then
              .node lk ll (.node k lr r)
            else if x < lk then
              match splay x ll with
              | .nil => .node lk ll (.node k lr r)
              | .node d lll llr =>
                  .node d lll (.node lk llr (.node k lr r))
            else
              match splay x lr with
              | .nil => .node lk ll (.node k lr r)
              | .node d lrl lrr =>
                  .node d (.node lk ll lrl) (.node k lrr r)
      else
        match r with
        | .nil => .node k l r
        | .node rk rl rr =>
            if x = rk then
              .node rk (.node k l rl) rr
            else if rk < x then
              match splay x rr with
              | .nil => .node rk (.node k l rl) rr
              | .node d rrl rrr =>
                  .node d (.node rk (.node k l rl) rrl) rrr
            else
              match splay x rl with
              | .nil => .node rk (.node k l rl) rr
              | .node d rll rlr =>
                  .node d (.node k l rll) (.node rk rlr rr)

/-- Splaying the empty tree is empty. -/
@[simp] public theorem splay_nil {α : Type u} [LinearOrder α] (x : α) :
    splay x (.nil : BinaryTree α) = .nil :=
  rfl

private theorem splay_node_self {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h : x = k) :
    splay x (.node k l r) = .node k l r := by
  unfold splay
  simp [h]

private theorem splay_node_left_nil {α : Type u} [LinearOrder α]
    {x k : α} {r : BinaryTree α} (h1 : x ≠ k) (h2 : x < k) :
    splay x (.node k .nil r) = .node k .nil r := by
  unfold splay
  simp [h1, h2]

private theorem splay_zig_left {α : Type u} [LinearOrder α]
    {x k lk : α} {ll lr r : BinaryTree α}
    (h1 : x ≠ k) (h2 : x < k) (h3 : x = lk) :
    splay x (.node k (.node lk ll lr) r) = .node lk ll (.node k lr r) := by
  subst h3
  unfold splay
  rw [ite_eq_right h1, ite_eq_left h2]
  dsimp only
  rw [ite_eq_left rfl]

private theorem splay_zigzig_left_nil {α : Type u} [LinearOrder α]
    {x k lk : α} {ll lr r : BinaryTree α}
    (h1 : x ≠ k) (h2 : x < k) (h3 : x ≠ lk) (h4 : x < lk)
    (hll : splay x ll = .nil) :
    splay x (.node k (.node lk ll lr) r) = .node lk ll (.node k lr r) := by
  unfold splay
  simp [h1, h2, h3, h4, hll]

private theorem splay_zigzig_left_node {α : Type u} [LinearOrder α]
    {x k lk d : α} {ll lr r lll llr : BinaryTree α}
    (h1 : x ≠ k) (h2 : x < k) (h3 : x ≠ lk) (h4 : x < lk)
    (hll : splay x ll = .node d lll llr) :
    splay x (.node k (.node lk ll lr) r) =
      .node d lll (.node lk llr (.node k lr r)) := by
  unfold splay
  simp [h1, h2, h3, h4, hll]

private theorem splay_zigzag_left_nil {α : Type u} [LinearOrder α]
    {x k lk : α} {ll lr r : BinaryTree α}
    (h1 : x ≠ k) (h2 : x < k) (h3 : x ≠ lk) (h4 : ¬x < lk)
    (hlr : splay x lr = .nil) :
    splay x (.node k (.node lk ll lr) r) = .node lk ll (.node k lr r) := by
  unfold splay
  simp [h1, h2, h3, h4, hlr]

private theorem splay_zigzag_left_node {α : Type u} [LinearOrder α]
    {x k lk d : α} {ll lr r lrl lrr : BinaryTree α}
    (h1 : x ≠ k) (h2 : x < k) (h3 : x ≠ lk) (h4 : ¬x < lk)
    (hlr : splay x lr = .node d lrl lrr) :
    splay x (.node k (.node lk ll lr) r) =
      .node d (.node lk ll lrl) (.node k lrr r) := by
  unfold splay
  simp [h1, h2, h3, h4, hlr]

private theorem splay_node_right_nil {α : Type u} [LinearOrder α]
    {x k : α} {l : BinaryTree α} (h1 : x ≠ k) (h2 : ¬x < k) :
    splay x (.node k l .nil) = .node k l .nil := by
  unfold splay
  simp [h1, h2]

private theorem splay_zig_right {α : Type u} [LinearOrder α]
    {x k rk : α} {l rl rr : BinaryTree α}
    (h1 : x ≠ k) (h2 : ¬x < k) (h3 : x = rk) :
    splay x (.node k l (.node rk rl rr)) = .node rk (.node k l rl) rr := by
  subst h3
  unfold splay
  rw [ite_eq_right h1, ite_eq_right h2]
  dsimp only
  rw [ite_eq_left rfl]

private theorem splay_zigzig_right_nil {α : Type u} [LinearOrder α]
    {x k rk : α} {l rl rr : BinaryTree α}
    (h1 : x ≠ k) (h2 : ¬x < k) (h3 : x ≠ rk) (h4 : rk < x)
    (hrr : splay x rr = .nil) :
    splay x (.node k l (.node rk rl rr)) =
      .node rk (.node k l rl) rr := by
  unfold splay
  simp [h1, h2, h3, h4, hrr]

private theorem splay_zigzig_right_node {α : Type u} [LinearOrder α]
    {x k rk d : α} {l rl rr rrl rrr : BinaryTree α}
    (h1 : x ≠ k) (h2 : ¬x < k) (h3 : x ≠ rk) (h4 : rk < x)
    (hrr : splay x rr = .node d rrl rrr) :
    splay x (.node k l (.node rk rl rr)) =
      .node d (.node rk (.node k l rl) rrl) rrr := by
  unfold splay
  simp [h1, h2, h3, h4, hrr]

private theorem splay_zigzag_right_nil {α : Type u} [LinearOrder α]
    {x k rk : α} {l rl rr : BinaryTree α}
    (h1 : x ≠ k) (h2 : ¬x < k) (h3 : x ≠ rk) (h4 : ¬rk < x)
    (hrl : splay x rl = .nil) :
    splay x (.node k l (.node rk rl rr)) =
      .node rk (.node k l rl) rr := by
  unfold splay
  simp [h1, h2, h3, h4, hrl]

private theorem splay_zigzag_right_node {α : Type u} [LinearOrder α]
    {x k rk d : α} {l rl rr rll rlr : BinaryTree α}
    (h1 : x ≠ k) (h2 : ¬x < k) (h3 : x ≠ rk) (h4 : ¬rk < x)
    (hrl : splay x rl = .node d rll rlr) :
    splay x (.node k l (.node rk rl rr)) =
      .node d (.node k l rll) (.node rk rlr rr) := by
  unfold splay
  simp [h1, h2, h3, h4, hrl]

private theorem all_mono {α : Type u} {p q : α → Prop}
    (h : ∀ y, p y → q y) {t : BinaryTree α} (ht : All p t) : All q t := by
  rw [all_iff_forall_mem] at ht ⊢
  exact fun y hy => h y (ht y hy)

private theorem mem_left_of_lt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α}
    (hOrd : Ordered (.node k l r))
    (hx : x ∈ BinaryTree.node k l r) (hlt : x < k) : x ∈ l := by
  rcases hOrd with ⟨_, _, _, hAllRight⟩
  rcases hx with hx | hx | hx
  · exact hx
  · exact absurd (hx ▸ hlt) (lt_irrefl k)
  · exact (lt_asymm hlt ((all_iff_forall_mem.mp hAllRight) x hx)).elim

private theorem mem_right_of_gt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α}
    (hOrd : Ordered (.node k l r))
    (hx : x ∈ BinaryTree.node k l r) (hgt : k < x) : x ∈ r := by
  rcases hOrd with ⟨_, _, hAllLeft, _⟩
  rcases hx with hx | hx | hx
  · exact (lt_asymm hgt ((all_iff_forall_mem.mp hAllLeft) x hx)).elim
  · exact absurd (hx ▸ hgt) (lt_irrefl k)
  · exact hx

private theorem mem_of_root?_eq_some {α : Type u} {x : α}
    {t : BinaryTree α} (h : root? t = some x) : x ∈ t := by
  cases t with
  | nil => simp [root?] at h
  | node k l r =>
      have hk : k = x := by simpa [root?] using h
      exact Or.inr (Or.inl hk.symm)

private theorem inorder_splay_aux {α : Type u} [LinearOrder α] {x : α}
    (n : Nat) (t : BinaryTree α) (h : t.numNodes ≤ n) :
    inorder (splay x t) = inorder t := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil => rfl
      | node k l r =>
          simp only [BinaryTree.numNodes] at h
          omega
  | succ n ih =>
      cases t with
      | nil => rfl
      | node k l r =>
          by_cases hxk : x = k
          · rw [splay_node_self hxk]
          · by_cases hlt : x < k
            · cases l with
              | nil => rw [splay_node_left_nil hxk hlt]
              | node lk ll lr =>
                  by_cases hxl : x = lk
                  · rw [splay_zig_left hxk hlt hxl]
                    simp [List.append_assoc]
                  · by_cases hllt : x < lk
                    · cases hs : splay x ll with
                      | nil =>
                          have hb : ll.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIl : inorder ll = [] := by
                            have hh := ih ll hb
                            rw [hs] at hh
                            simpa using hh.symm
                          rw [splay_zigzig_left_nil hxk hlt hxl hllt hs]
                          simp [hIl, List.append_assoc]
                      | node d lll llr =>
                          have hb : ll.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIl : inorder ll =
                              inorder lll ++ d :: inorder llr := by
                            have hh := ih ll hb
                            rw [hs] at hh
                            rw [← hh, inorder_node]
                          rw [splay_zigzig_left_node hxk hlt hxl hllt hs]
                          simp [hIl, List.append_assoc]
                    · cases hs : splay x lr with
                      | nil =>
                          have hb : lr.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIl : inorder lr = [] := by
                            have hh := ih lr hb
                            rw [hs] at hh
                            simpa using hh.symm
                          rw [splay_zigzag_left_nil hxk hlt hxl hllt hs]
                          simp [hIl, List.append_assoc]
                      | node d lrl lrr =>
                          have hb : lr.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIl : inorder lr =
                              inorder lrl ++ d :: inorder lrr := by
                            have hh := ih lr hb
                            rw [hs] at hh
                            rw [← hh, inorder_node]
                          rw [splay_zigzag_left_node hxk hlt hxl hllt hs]
                          simp [hIl, List.append_assoc]
            · cases r with
              | nil => rw [splay_node_right_nil hxk hlt]
              | node rk rl rr =>
                  by_cases hxr : x = rk
                  · rw [splay_zig_right hxk hlt hxr]
                    simp [List.append_assoc]
                  · by_cases hrrt : rk < x
                    · cases hs : splay x rr with
                      | nil =>
                          have hb : rr.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIr : inorder rr = [] := by
                            have hh := ih rr hb
                            rw [hs] at hh
                            simpa using hh.symm
                          rw [splay_zigzig_right_nil hxk hlt hxr hrrt hs]
                          simp [hIr, List.append_assoc]
                      | node d rrl rrr =>
                          have hb : rr.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIr : inorder rr =
                              inorder rrl ++ d :: inorder rrr := by
                            have hh := ih rr hb
                            rw [hs] at hh
                            rw [← hh, inorder_node]
                          rw [splay_zigzig_right_node hxk hlt hxr hrrt hs]
                          simp [hIr, List.append_assoc]
                    · cases hs : splay x rl with
                      | nil =>
                          have hb : rl.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIr : inorder rl = [] := by
                            have hh := ih rl hb
                            rw [hs] at hh
                            simpa using hh.symm
                          rw [splay_zigzag_right_nil hxk hlt hxr hrrt hs]
                          simp [hIr, List.append_assoc]
                      | node d rll rlr =>
                          have hb : rl.numNodes ≤ n := by
                            simp only [BinaryTree.numNodes] at h
                            omega
                          have hIr : inorder rl =
                              inorder rll ++ d :: inorder rlr := by
                            have hh := ih rl hb
                            rw [hs] at hh
                            rw [← hh, inorder_node]
                          rw [splay_zigzag_right_node hxk hlt hxr hrrt hs]
                          simp [hIr, List.append_assoc]

/-- Splaying preserves the inorder traversal exactly (in particular it is
a permutation of the original traversal). -/
public theorem inorder_splay {α : Type u} [LinearOrder α] {x : α}
    (t : BinaryTree α) : inorder (splay x t) = inorder t :=
  inorder_splay_aux t.numNodes t (by omega)

/-- Splaying preserves structural membership. -/
public theorem mem_splay {α : Type u} [LinearOrder α] {x y : α}
    {t : BinaryTree α} : y ∈ splay x t ↔ y ∈ t := by
  simp only [← mem_inorder, inorder_splay]

/-- Splaying preserves the number of nodes. -/
public theorem numNodes_splay {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} : (splay x t).numNodes = t.numNodes := by
  rw [numNodes_eq_length_inorder, numNodes_eq_length_inorder,
    inorder_splay]

private theorem ordered_of_pairwise_inorder {α : Type u}
    [LinearOrder α] {t : BinaryTree α}
    (h : (inorder t).Pairwise (· < ·)) : Ordered t := by
  induction t with
  | nil => trivial
  | node k l r ihl ihr =>
      rw [inorder_node, List.pairwise_append] at h
      obtain ⟨hL, hKR, hLR⟩ := h
      rw [List.pairwise_cons] at hKR
      obtain ⟨hkR, hR⟩ := hKR
      refine ⟨ihl hL, ihr hR, ?_, ?_⟩
      · rw [all_iff_forall_mem]
        intro y hy
        exact hLR y (mem_inorder.mpr hy) k List.mem_cons_self
      · rw [all_iff_forall_mem]
        intro y hy
        exact hkR y (mem_inorder.mpr hy)

/-- Splaying preserves the strict search-tree invariant. -/
public theorem ordered_splay {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (h : Ordered t) : Ordered (splay x t) :=
  ordered_of_pairwise_inorder (by
    rw [inorder_splay]
    exact ordered_inorder h)

private theorem splay_eq_node_aux {α : Type u} [LinearOrder α] {x : α}
    (n : Nat) (t : BinaryTree α) (h : t.numNodes ≤ n)
    (hOrd : Ordered t) (hx : x ∈ t) :
    ∃ l r, splay x t = .node x l r := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil => simp at hx
      | node k l r =>
          simp only [BinaryTree.numNodes] at h
          omega
  | succ n ih =>
      cases t with
      | nil => simp at hx
      | node k l r =>
          rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
          by_cases hxk : x = k
          · obtain rfl : k = x := hxk.symm
            rw [splay_node_self rfl]
            exact ⟨l, r, rfl⟩
          · by_cases hlt : x < k
            · have hxL : x ∈ l :=
                mem_left_of_lt ⟨hOrdL, hOrdR, hAllL, hAllR⟩ hx hlt
              cases l with
              | nil => simp at hxL
              | node lk ll lr =>
                  rcases hOrdL with ⟨hOrdLL, hOrdLR, hAllLL, hAllLR⟩
                  by_cases hxl : x = lk
                  · rw [splay_zig_left hxk hlt hxl]
                    exact ⟨ll, .node k lr r, by rw [hxl]⟩
                  · by_cases hllt : x < lk
                    · have hxLL : x ∈ ll :=
                        mem_left_of_lt ⟨hOrdLL, hOrdLR, hAllLL, hAllLR⟩
                          hxL hllt
                      have hb : ll.numNodes ≤ n := by
                        simp only [BinaryTree.numNodes] at h
                        omega
                      obtain ⟨l', r', hs⟩ := ih ll hb hOrdLL hxLL
                      cases hs' : splay x ll with
                      | nil =>
                          rw [hs'] at hs
                          cases hs
                      | node d lll llr =>
                          rw [hs'] at hs
                          obtain ⟨hd, -, -⟩ := BinaryTree.node.inj hs
                          rw [splay_zigzig_left_node hxk hlt hxl hllt hs']
                          exact ⟨lll, .node lk llr (.node k lr r),
                            by rw [hd]⟩
                    · have hgt : lk < x :=
                        lt_of_le_of_ne (le_of_not_gt hllt)
                          (fun hh => hxl hh.symm)
                      have hxLR : x ∈ lr :=
                        mem_right_of_gt ⟨hOrdLL, hOrdLR, hAllLL, hAllLR⟩
                          hxL hgt
                      have hb : lr.numNodes ≤ n := by
                        simp only [BinaryTree.numNodes] at h
                        omega
                      obtain ⟨l', r', hs⟩ := ih lr hb hOrdLR hxLR
                      cases hs' : splay x lr with
                      | nil =>
                          rw [hs'] at hs
                          cases hs
                      | node d lrl lrr =>
                          rw [hs'] at hs
                          obtain ⟨hd, -, -⟩ := BinaryTree.node.inj hs
                          rw [splay_zigzag_left_node hxk hlt hxl hllt hs']
                          exact ⟨.node lk ll lrl, .node k lrr r,
                            by rw [hd]⟩
            · have hgt : k < x :=
                lt_of_le_of_ne (le_of_not_gt hlt) (fun hh => hxk hh.symm)
              have hxR : x ∈ r :=
                mem_right_of_gt ⟨hOrdL, hOrdR, hAllL, hAllR⟩ hx hgt
              cases r with
              | nil => simp at hxR
              | node rk rl rr =>
                  rcases hOrdR with ⟨hOrdRL, hOrdRR, hAllRL, hAllRR⟩
                  by_cases hxr : x = rk
                  · rw [splay_zig_right hxk hlt hxr]
                    exact ⟨.node k l rl, rr, by rw [hxr]⟩
                  · by_cases hrrt : rk < x
                    · have hxRR : x ∈ rr :=
                        mem_right_of_gt ⟨hOrdRL, hOrdRR, hAllRL, hAllRR⟩
                          hxR hrrt
                      have hb : rr.numNodes ≤ n := by
                        simp only [BinaryTree.numNodes] at h
                        omega
                      obtain ⟨l', r', hs⟩ := ih rr hb hOrdRR hxRR
                      cases hs' : splay x rr with
                      | nil =>
                          rw [hs'] at hs
                          cases hs
                      | node d rrl rrr =>
                          rw [hs'] at hs
                          obtain ⟨hd, -, -⟩ := BinaryTree.node.inj hs
                          rw [splay_zigzig_right_node hxk hlt hxr hrrt hs']
                          exact ⟨.node rk (.node k l rl) rrl, rrr,
                            by rw [hd]⟩
                    · have hxlt : x < rk :=
                        lt_of_le_of_ne (le_of_not_gt hrrt) hxr
                      have hxRL : x ∈ rl :=
                        mem_left_of_lt ⟨hOrdRL, hOrdRR, hAllRL, hAllRR⟩
                          hxR hxlt
                      have hb : rl.numNodes ≤ n := by
                        simp only [BinaryTree.numNodes] at h
                        omega
                      obtain ⟨l', r', hs⟩ := ih rl hb hOrdRL hxRL
                      cases hs' : splay x rl with
                      | nil =>
                          rw [hs'] at hs
                          cases hs
                      | node d rll rlr =>
                          rw [hs'] at hs
                          obtain ⟨hd, -, -⟩ := BinaryTree.node.inj hs
                          rw [splay_zigzag_right_node hxk hlt hxr hrrt hs']
                          exact ⟨.node k l rll, .node rk rlr rr,
                            by rw [hd]⟩

/-- Splaying a present key of an ordered tree brings it to the root. -/
public theorem root_splay_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    ∃ l r, splay x t = .node x l r :=
  splay_eq_node_aux t.numNodes t (by omega) hOrd hx

/-- The root after splaying a present key is that key. -/
public theorem root?_splay_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    root? (splay x t) = some x := by
  obtain ⟨l, r, h⟩ := root_splay_of_mem hOrd hx
  rw [h]
  rfl

/--
Split a tree at `x` into keys below `x` and keys above `x`, dropping `x`
itself if present. This is the plain search-tree split; `insert` applies
it to the splayed tree.
-/
public def split {α : Type u} [LinearOrder α] (x : α) :
    BinaryTree α → BinaryTree α × BinaryTree α
  | .nil => (.nil, .nil)
  | .node k l r =>
      if x < k then
        match split x l with
        | (ll, lr) => (ll, .node k lr r)
      else if k < x then
        match split x r with
        | (rl, rr) => (.node k l rl, rr)
      else (l, r)

private theorem split_node_lt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h : x < k) :
    split x (.node k l r) = ((split x l).1, .node k (split x l).2 r) := by
  cases h' : split x l with
  | mk ll lr => simp [split, h, h']

private theorem split_node_gt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h1 : ¬x < k) (h2 : k < x) :
    split x (.node k l r) = (.node k l (split x r).1, (split x r).2) := by
  cases h' : split x r with
  | mk rl rr => simp [split, h1, h2, h']

private theorem split_node_eq {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h1 : ¬x < k) (h2 : ¬k < x) :
    split x (.node k l r) = (l, r) := by
  simp [split, h1, h2]

private theorem split_fst_lt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h : x < k) :
    (split x (.node k l r)).1 = (split x l).1 := by
  rw [split_node_lt h]

private theorem split_snd_lt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h : x < k) :
    (split x (.node k l r)).2 = .node k (split x l).2 r := by
  rw [split_node_lt h]

private theorem split_fst_gt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h1 : ¬x < k) (h2 : k < x) :
    (split x (.node k l r)).1 = .node k l (split x r).1 := by
  rw [split_node_gt h1 h2]

private theorem split_snd_gt {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h1 : ¬x < k) (h2 : k < x) :
    (split x (.node k l r)).2 = (split x r).2 := by
  rw [split_node_gt h1 h2]

private theorem split_fst_eq {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h1 : ¬x < k) (h2 : ¬k < x) :
    (split x (.node k l r)).1 = l := by
  rw [split_node_eq h1 h2]

private theorem split_snd_eq {α : Type u} [LinearOrder α]
    {x k : α} {l r : BinaryTree α} (h1 : ¬x < k) (h2 : ¬k < x) :
    (split x (.node k l r)).2 = r := by
  rw [split_node_eq h1 h2]

/-- Every key of a split part is a key of the original tree. -/
public theorem mem_of_mem_split {α : Type u} [LinearOrder α]
    {x y : α} {t : BinaryTree α} :
    y ∈ (split x t).1 ∨ y ∈ (split x t).2 → y ∈ t := by
  induction t with
  | nil =>
      intro h
      rcases h with h | h <;> exact h
  | node k l r ihl ihr =>
      intro h
      by_cases h1 : x < k
      · rw [split_fst_lt h1, split_snd_lt h1] at h
        rcases h with h | h
        · exact Or.inl (ihl (Or.inl h))
        · rcases h with h | h | h
          · exact Or.inl (ihl (Or.inr h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · by_cases h2 : k < x
        · rw [split_fst_gt h1 h2, split_snd_gt h1 h2] at h
          rcases h with h | h
          · rcases h with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (ihr (Or.inl h)))
          · exact Or.inr (Or.inr (ihr (Or.inr h)))
        · rw [split_fst_eq h1 h2, split_snd_eq h1 h2] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

/-- Every key other than the split key survives into one of the parts. -/
public theorem mem_split_of_mem {α : Type u} [LinearOrder α]
    {x y : α} {t : BinaryTree α} (h : y ∈ t) (hyx : y ≠ x) :
    y ∈ (split x t).1 ∨ y ∈ (split x t).2 := by
  induction t with
  | nil => exact h.elim
  | node k l r ihl ihr =>
      by_cases h1 : x < k
      · rw [split_fst_lt h1, split_snd_lt h1]
        rcases h with h | h | h
        · rcases ihl h with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · by_cases h2 : k < x
        · rw [split_fst_gt h1 h2, split_snd_gt h1 h2]
          rcases h with h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · rcases ihr h with hh | hh
            · exact Or.inl (Or.inr (Or.inr hh))
            · exact Or.inr hh
        · rw [split_fst_eq h1 h2, split_snd_eq h1 h2]
          have hxk : x = k := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          rcases h with h | h | h
          · exact Or.inl h
          · exact (hyx (h.trans hxk.symm)).elim
          · exact Or.inr h

/-- In an ordered tree, the left split part lies below `x` and the right
part lies above `x`. -/
public theorem all_split {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) :
    All (· < x) (split x t).1 ∧ All (x < ·) (split x t).2 := by
  induction t with
  | nil => exact ⟨trivial, trivial⟩
  | node k l r ihl ihr =>
      rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
      by_cases h1 : x < k
      · rw [split_fst_lt h1, split_snd_lt h1]
        obtain ⟨hL1, hL2⟩ := ihl hOrdL
        exact ⟨hL1, hL2, h1, all_mono (fun y hy => lt_trans h1 hy) hAllR⟩
      · by_cases h2 : k < x
        · rw [split_fst_gt h1 h2, split_snd_gt h1 h2]
          obtain ⟨hR1, hR2⟩ := ihr hOrdR
          exact ⟨⟨all_mono (fun y hy => lt_trans hy h2) hAllL, h2, hR1⟩,
            hR2⟩
        · have hxk : x = k :=
            le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          rw [split_fst_eq h1 h2, split_snd_eq h1 h2]
          subst hxk
          exact ⟨hAllL, hAllR⟩

/-- Splitting an ordered tree yields two ordered trees. -/
public theorem ordered_split {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) :
    Ordered (split x t).1 ∧ Ordered (split x t).2 := by
  induction t with
  | nil => exact ⟨trivial, trivial⟩
  | node k l r ihl ihr =>
      rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
      by_cases h1 : x < k
      · rw [split_fst_lt h1, split_snd_lt h1]
        obtain ⟨ho1, ho2⟩ := ihl hOrdL
        refine ⟨ho1, ho2, hOrdR, ?_, hAllR⟩
        rw [all_iff_forall_mem] at hAllL ⊢
        exact fun y hy => hAllL y (mem_of_mem_split (Or.inr hy))
      · by_cases h2 : k < x
        · rw [split_fst_gt h1 h2, split_snd_gt h1 h2]
          obtain ⟨ho1, ho2⟩ := ihr hOrdR
          refine ⟨⟨hOrdL, ho1, hAllL, ?_⟩, ho2⟩
          rw [all_iff_forall_mem] at hAllR ⊢
          exact fun y hy => hAllR y (mem_of_mem_split (Or.inl hy))
        · rw [split_fst_eq h1 h2, split_snd_eq h1 h2]
          exact ⟨hOrdL, hOrdR⟩

/--
Insert a key by splaying and then splitting: splay `x`, split the result
at `x`, and attach the two parts below a fresh root holding `x`. An
already-present key is splayed to the root and split off, so no duplicate
is created.
-/
public def insert {α : Type u} [LinearOrder α] (x : α)
    (t : BinaryTree α) : BinaryTree α :=
  let p := split x (splay x t)
  .node x p.1 p.2

private theorem insert_eq {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} :
    insert x t = .node x (split x (splay x t)).1 (split x (splay x t)).2 :=
  rfl

/-- Access a key: splay it and report whether it reached the root,
together with the restructured tree. -/
public def access {α : Type u} [LinearOrder α] (x : α)
    (t : BinaryTree α) : Bool × BinaryTree α :=
  let t' := splay x t
  (decide (root? t' = some x), t')

/-- Membership test via splay: splay the key and inspect the root. -/
public def contains {α : Type u} [LinearOrder α] (x : α)
    (t : BinaryTree α) : Bool :=
  (access x t).1

/-- The tree returned by `access` is the splayed tree. -/
public theorem access_snd {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} : (access x t).2 = splay x t :=
  rfl

/-- Inserting a key adds exactly that key to structural membership. -/
public theorem mem_insert {α : Type u} [LinearOrder α] {x y : α}
    {t : BinaryTree α} : y ∈ insert x t ↔ y = x ∨ y ∈ t := by
  rw [insert_eq]
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inr (mem_splay.mp (mem_of_mem_split (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (mem_splay.mp (mem_of_mem_split (Or.inr h)))
  · rintro (rfl | h)
    · exact Or.inr (Or.inl rfl)
    · by_cases hyx : y = x
      · subst hyx
        exact Or.inr (Or.inl rfl)
      · rcases mem_split_of_mem (mem_splay.mpr h) hyx with hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inr hh)

/-- Insertion preserves the strict search-tree invariant. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (h : Ordered t) : Ordered (insert x t) := by
  rw [insert_eq]
  have hs : Ordered (splay x t) := ordered_splay h
  obtain ⟨ho1, ho2⟩ := ordered_split (t := splay x t) hs
  obtain ⟨ha1, ha2⟩ := all_split (t := splay x t) hs
  exact ⟨ho1, ho2, ha1, ha2⟩

/-- The inserted key is the root of the result. -/
public theorem root?_insert {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} : root? (insert x t) = some x := by
  rw [insert_eq]
  rfl

/-- `contains` agrees with structural membership for an ordered tree. -/
public theorem contains_eq_true_iff {α : Type u} [LinearOrder α]
    {x : α} {t : BinaryTree α} (hOrd : Ordered t) :
    contains x t = true ↔ x ∈ t := by
  show decide (root? (splay x t) = some x) = true ↔ x ∈ t
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact mem_splay.mp (mem_of_root?_eq_some h)
  · intro h
    exact root?_splay_of_mem hOrd h

end SplayTree
end Cslib.Algorithms.Lean
