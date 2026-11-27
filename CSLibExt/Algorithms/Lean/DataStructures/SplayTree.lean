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

`splay x t` searches for `x` as in a binary search tree and rotates the
found node (or the last node visited) to the root with the three splaying
cases: zig (single rotation), zig-zig (rotate the grandparent-parent edge
first), and zig-zag (rotate the parent-node edge first). The definition
pattern-matches two levels of the tree at once, recursing into the relevant
grandchild, so rotations are paired starting from the root: when the search
path has an odd number of edges, the single rotation is done on its last
edge rather than at the root as in Sleator and Tarjan's bottom-up splaying,
and the resulting tree can differ from theirs. `insert`
splays the key and then splits, `access` splays and reports whether the
key reached the root, and `contains` is its Boolean projection.

The module proves functional correctness only: splaying preserves the
inorder traversal (hence membership and `Ordered`), and a present key
ends at the root. The amortized `O(log n)` access lemma (the
Sleator-Tarjan potential argument) for this definition is proved in
`CSLibExt.Algorithms.Lean.DataStructures.SplayTree.Amortized`.

It also provides `splayMax` (splay the rightmost key to the root; it is the
maximum key when the tree is `Ordered`), `delete` (splay, then replace a
present key by the maximum of the left subtree),
and `nipkowInsert` (the book's insert: splay, then rebuild around the new
root; it computes the same tree as `insert`, by `insert_eq_nipkowInsert`),
with the same functional-correctness guarantees (Nipkow, FDSA §21.1);
their amortized bounds are in
`CSLibExt.Algorithms.Lean.DataStructures.SplayTree.Amortized`.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace SplayTree

open BinarySearchTree

/-- **Root key of a splay tree.** The optional root key of a binary tree is undefined (none) for
the empty tree, and is the key $k$ for a tree whose root node holds $k$. -/
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
**Splay operation.** Let $\alpha$ be a linearly ordered type and write $(k; L, R)$ for the binary
tree with root key $k$, left subtree $L$ and right subtree $R$. For $x \in \alpha$, the splay
$S_x(t)$ of a binary tree $t$ with keys in $\alpha$ is defined by recursion on $t$. The empty tree
splays to itself, and $t = (k; L, R)$ is left unchanged if $x = k$, if $x < k$ and $L$ is empty,
or if $x > k$ and $R$ is empty. If $x < k$ and $L = (a; A, B)$, then: if $x = a$, the result is
the zig $(a; A, (k; B, R))$; if $x < a$ and $S_x(A) = (d; A_1, A_2)$, the result is the zig-zig
$(d; A_1, (a; A_2, (k; B, R)))$; if $x > a$ and $S_x(B) = (d; B_1, B_2)$, the result is the
zig-zag $(d; (a; A, B_1), (k; B_2, R))$; and if the splayed subtree $S_x(A)$, respectively
$S_x(B)$, is empty, the result is the zig $(a; A, (k; B, R))$. The case $x > k$ with
$R = (b; C, D)$ is the mirror image: if $x = b$, the result is the zig $(b; (k; L, C), D)$; if
$x > b$ and $S_x(D) = (d; D_1, D_2)$, it is the zig-zig $(d; (b; (k; L, C), D_1), D_2)$; if
$x < b$ and $S_x(C) = (d; C_1, C_2)$, it is the zig-zag $(d; (k; L, C_1), (b; C_2, D))$; and if
the splayed subtree is empty, it is the zig $(b; (k; L, C), D)$.

The search path for $x$ runs from the root to the node with key $x$, or to the last node visited
if $x$ is absent. Each recursive step consumes two edges of this path, starting at the root, so
when the path has an odd number of edges the single rotation is performed on its last edge, the
one farthest from the root.
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

/-- **Splaying the empty tree.** For every key $x$ of a linearly ordered type, splaying $x$ in the
empty binary tree gives the empty tree. -/
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
                          simp [hIl]
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

/-- **Splaying preserves the inorder traversal.** For every key $x$ and every binary tree $t$
over a linearly ordered type, the inorder traversal of the tree obtained by splaying $x$ in $t$
equals the inorder traversal of $t$. No search-tree ordering of $t$ is assumed. -/
public theorem inorder_splay {α : Type u} [LinearOrder α] {x : α}
    (t : BinaryTree α) : inorder (splay x t) = inorder t :=
  inorder_splay_aux t.numNodes t (by omega)

/-- **Splaying preserves membership.** For keys $x$ and $y$ and a binary tree $t$ over a linearly
ordered type, $y$ is a key of the tree obtained by splaying $x$ in $t$ if and only if $y$ is a
key of $t$. -/
public theorem mem_splay {α : Type u} [LinearOrder α] {x y : α}
    {t : BinaryTree α} : y ∈ splay x t ↔ y ∈ t := by
  simp only [← mem_inorder, inorder_splay]

/-- **Splaying preserves the number of nodes.** For every binary tree $t$ with keys in a linearly
ordered type and every key $x$, the tree obtained by splaying $x$ in $t$ has the same number of
nodes as $t$. -/
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

/-- **Splaying preserves the search-tree property.** Let $t$ be a binary tree with keys in a
linearly ordered type and let $x$ be a key. If $t$ is a binary search tree (at every node, every
key of the left subtree is strictly smaller and every key of the right subtree strictly larger
than the key of the node), then the tree obtained by splaying $x$ in $t$ is again a binary search
tree. -/
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

/-- **Splaying a present key brings it to the root.** Let $t$ be a binary search tree with keys in
a linearly ordered type (at every node, every key of the left subtree is strictly smaller and
every key of the right subtree strictly larger than the key of the node), and let $x$ be a key
that occurs in $t$. Then there are binary trees $l$ and $r$ such that splaying $x$ in $t$ gives
the tree whose root holds $x$, with left subtree $l$ and right subtree $r$. -/
public theorem root_splay_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    ∃ l r, splay x t = .node x l r :=
  splay_eq_node_aux t.numNodes t (by omega) hOrd hx

/-- **Root key after splaying a present key.** Let $t$ be a binary search tree with keys in a
linearly ordered type (at every node, every key of the left subtree is strictly smaller and every
key of the right subtree strictly larger than the key of the node), and let $x$ be a key that
occurs in $t$. Then the tree obtained by splaying $x$ in $t$ is nonempty and its root key is $x$. -/
public theorem root?_splay_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    root? (splay x t) = some x := by
  obtain ⟨l, r, h⟩ := root_splay_of_mem hOrd hx
  rw [h]
  rfl

/--
**Search-path split at a key.** Let $\alpha$ be a linearly ordered type, let $x \in \alpha$, and
write $(k; L, R)$ for the binary tree with root key $k$, left subtree $L$ and right subtree $R$.
The split of a binary tree with keys in $\alpha$ at $x$ is the pair of trees defined by
recursion: the empty tree splits into two empty trees; if $x < k$ and $L$ splits into
$(L_1, L_2)$, then $(k; L, R)$ splits into $(L_1, (k; L_2, R))$; if $k < x$ and $R$ splits into
$(R_1, R_2)$, then $(k; L, R)$ splits into $((k; L, R_1), R_2)$; and if $x = k$, then
$(k; L, R)$ splits into $(L, R)$.

When the tree is a binary search tree (at every node, the keys of the left subtree are strictly
smaller and those of the right subtree strictly larger than the node's key), the first part
holds the keys below $x$ and the second part the keys above $x$; the key $x$, if present, is
dropped.
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

/-- **Splay-tree split parts contain only original keys.** For keys $x$ and $y$ and a binary
tree $t$ over a linearly ordered type, if $y$ is a key of the left part or of the right part of
the split of $t$ at $x$, then $y$ is a key of $t$. -/
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

/-- **Keys other than the split key survive a split.** Let $t$ be a binary tree with keys in a
linearly ordered type, and let $x$ and $y$ be keys with $y \ne x$. If $y$ occurs as a key of $t$,
then $y$ occurs as a key of the left part or of the right part of the split of $t$ at $x$.
The tree $t$ need not be a binary search tree. -/
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

/-- **Splitting an ordered tree separates the keys around the split key.** Let $t$ be an ordered
binary tree over a linearly ordered type and let $x$ be a key. When $t$ is split at $x$, every
key of the left part is strictly less than $x$ and every key of the right part is strictly
greater than $x$. -/
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

/-- **Both parts of a split search tree are search trees.** Let $t$ be a binary tree with keys in a
linearly ordered type and let $x$ be a key. If $t$ is a binary search tree (at every node, every
key of the left subtree is strictly smaller and every key of the right subtree strictly larger
than the key of the node), then the left part and the right part of the split of $t$ at $x$ are
both binary search trees. -/
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
**Splay-tree insertion.** For a key $x$ and a binary tree $t$ over a linearly ordered type,
inserting $x$ into $t$ splays $x$ in $t$, splits the resulting tree at $x$ into a left part and
a right part, and returns the tree whose root key is $x$, whose left subtree is the left part
and whose right subtree is the right part.

In an ordered tree that already contains $x$, the key is splayed to the root and dropped by the
split, so no duplicate is created.
-/
public def insert {α : Type u} [LinearOrder α] (x : α)
    (t : BinaryTree α) : BinaryTree α :=
  let p := split x (splay x t)
  .node x p.1 p.2

private theorem insert_eq {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} :
    insert x t = .node x (split x (splay x t)).1 (split x (splay x t)).2 :=
  rfl

/-- **Splay-tree access.** For a key $x$ and a binary tree $t$ over a linearly ordered type, the
access of $x$ in $t$ is the pair $(b, t')$, where $t'$ is the tree obtained by splaying $x$ in
$t$ and $b$ is true exactly when $t'$ is nonempty and its root key is $x$. -/
public def access {α : Type u} [LinearOrder α] (x : α)
    (t : BinaryTree α) : Bool × BinaryTree α :=
  let t' := splay x t
  (decide (root? t' = some x), t')

/-- **Splay-tree membership test.** For a key $x$ and a binary tree $t$ over a linearly ordered
type, the membership test of $x$ in $t$ is the Boolean component of the access of $x$ in $t$:
it is true exactly when the tree obtained by splaying $x$ in $t$ is nonempty and its root key
is $x$. -/
public def contains {α : Type u} [LinearOrder α] (x : α)
    (t : BinaryTree α) : Bool :=
  (access x t).1

/-- **The tree returned by a splay-tree access.** For a key $x$ and a binary tree $t$ over a
linearly ordered type, the tree component of the access of $x$ in $t$ is the tree obtained by
splaying $x$ in $t$. -/
public theorem access_snd {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} : (access x t).2 = splay x t :=
  rfl

/-- **Keys after splay-tree insertion.** For keys $x$ and $y$ and a binary tree $t$ over a
linearly ordered type, $y$ is a key of the tree obtained by splay-tree insertion of $x$ into $t$
if and only if $y = x$ or $y$ is a key of $t$. -/
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

/-- **Splay-tree insertion preserves the search-tree property.** Let $t$ be a binary tree with keys
in a linearly ordered type and let $x$ be a key. If $t$ is a binary search tree (at every node,
every key of the left subtree is strictly smaller and every key of the right subtree strictly
larger than the key of the node), then the splay-tree insertion of $x$ into $t$ is again a binary
search tree. -/
public theorem ordered_insert {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (h : Ordered t) : Ordered (insert x t) := by
  rw [insert_eq]
  have hs : Ordered (splay x t) := ordered_splay h
  obtain ⟨ho1, ho2⟩ := ordered_split (t := splay x t) hs
  obtain ⟨ha1, ha2⟩ := all_split (t := splay x t) hs
  exact ⟨ho1, ho2, ha1, ha2⟩

/-- **Splay-tree insertion puts the inserted key at the root.** For every binary tree $t$ with keys
in a linearly ordered type and every key $x$, the splay-tree insertion of $x$ into $t$ is a
nonempty tree whose root key is $x$. -/
public theorem root?_insert {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} : root? (insert x t) = some x := by
  rw [insert_eq]
  rfl

/-- **Correctness of the splay-tree membership test.** For an ordered binary tree $t$ over a
linearly ordered type and a key $x$, the splay-tree membership test of $x$ in $t$ returns true
if and only if $x$ is a key of $t$. -/
public theorem contains_eq_true_iff {α : Type u} [LinearOrder α]
    {x : α} {t : BinaryTree α} (hOrd : Ordered t) :
    contains x t = true ↔ x ∈ t := by
  change decide (root? (splay x t) = some x) = true ↔ x ∈ t
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact mem_splay.mp (mem_of_root?_eq_some h)
  · intro h
    exact root?_splay_of_mem hOrd h

/--
Splay the rightmost key to the root (Nipkow's `splay_max`, FDSA §21.1); when the
tree is `Ordered`, the rightmost key is its maximum.
The recursion descends two levels down the right spine per step; when the
recursed subtree comes back empty, the single zig that carries its root
up is applied instead. No ordering is needed: the operation only follows
the right spine. The unreachable-looking empty branch of the match is
needed because `splayMax rr = .nil` can only be discharged once
`splayMax` is known to preserve nonemptiness (see `splayMax_ne_nil`).
-/
public def splayMax {α : Type u} : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node k l .nil => .node k l .nil
  | .node k l (.node rk rl rr) =>
    match splayMax rr with
    | .nil => .node rk (.node k l rl) .nil
    | .node c C D => .node c (.node rk (.node k l rl) C) D

/-- Splaying the empty tree for the maximum is empty. -/
@[simp] public theorem splayMax_nil {α : Type u} :
    splayMax (.nil : BinaryTree α) = .nil :=
  rfl

private theorem splayMax_node_node_of_nil {α : Type u}
    {k rk : α} {l rl rr : BinaryTree α} (h : splayMax rr = .nil) :
    splayMax (.node k l (.node rk rl rr)) = .node rk (.node k l rl) .nil := by
  unfold splayMax
  simp [h]

private theorem splayMax_node_node_of_node {α : Type u}
    {k rk c : α} {l rl rr C D : BinaryTree α} (h : splayMax rr = .node c C D) :
    splayMax (.node k l (.node rk rl rr)) =
      .node c (.node rk (.node k l rl) C) D := by
  unfold splayMax
  simp [h]

private theorem inorder_splayMax_aux {α : Type u} (n : Nat) (t : BinaryTree α)
    (h : t.numNodes ≤ n) : inorder (splayMax t) = inorder t := by
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
          cases r with
          | nil => rfl
          | node rk rl rr =>
              cases hs : splayMax rr with
              | nil =>
                  have hb : rr.numNodes ≤ n := by
                    simp only [BinaryTree.numNodes] at h
                    omega
                  have hIrr : inorder rr = [] := by
                    have hh := ih rr hb
                    rw [hs] at hh
                    simpa using hh.symm
                  rw [splayMax_node_node_of_nil hs]
                  simp [hIrr, List.append_assoc]
              | node c C D =>
                  have hb : rr.numNodes ≤ n := by
                    simp only [BinaryTree.numNodes] at h
                    omega
                  have hIrr : inorder rr = inorder C ++ c :: inorder D := by
                    have hh := ih rr hb
                    rw [hs] at hh
                    rw [← hh, inorder_node]
                  rw [splayMax_node_node_of_node hs]
                  simp [hIrr, List.append_assoc]

/-- Splaying the maximum preserves the inorder traversal exactly. -/
public theorem inorder_splayMax {α : Type u} (t : BinaryTree α) :
    inorder (splayMax t) = inorder t :=
  inorder_splayMax_aux t.numNodes t (by omega)

/-- Splaying the maximum preserves structural membership. -/
public theorem mem_splayMax {α : Type u} {x : α} {t : BinaryTree α} :
    x ∈ splayMax t ↔ x ∈ t := by
  simp only [← mem_inorder, inorder_splayMax]

/-- Splaying the maximum preserves the number of nodes. -/
public theorem numNodes_splayMax {α : Type u} {t : BinaryTree α} :
    (splayMax t).numNodes = t.numNodes := by
  rw [numNodes_eq_length_inorder, numNodes_eq_length_inorder, inorder_splayMax]

/-- Splaying the maximum preserves the strict search-tree invariant. -/
public theorem ordered_splayMax {α : Type u} [LinearOrder α] {t : BinaryTree α}
    (h : Ordered t) : Ordered (splayMax t) :=
  ordered_of_pairwise_inorder (by
    rw [inorder_splayMax]
    exact ordered_inorder h)

/-- Splaying the maximum returns the empty tree iff the input is empty. -/
public theorem splayMax_ne_nil {α : Type u} {t : BinaryTree α} (ht : t ≠ .nil) :
    splayMax t ≠ .nil := by
  intro hcon
  have h := numNodes_splayMax (t := t)
  rw [hcon] at h
  simp only [BinaryTree.numNodes] at h
  exact ht (by
    cases t with
    | nil => rfl
    | node k l r =>
      simp only [BinaryTree.numNodes] at h
      exact absurd h (by omega))

/-- Splaying the empty tree gives the empty tree, and vice versa. -/
public theorem splay_eq_nil {α : Type u} [LinearOrder α] {x : α} {t : BinaryTree α} :
    splay x t = .nil ↔ t = .nil := by
  constructor
  · intro h
    cases t with
    | nil => rfl
    | node k l r =>
      have hnum := numNodes_splay (x := x) (t := .node k l r)
      rw [h] at hnum
      simp only [BinaryTree.numNodes] at hnum
      omega
  · rintro rfl
    rfl

/-- Splaying the maximum of the empty tree gives the empty tree, and vice versa. -/
public theorem splayMax_eq_nil {α : Type u} {t : BinaryTree α} :
    splayMax t = .nil ↔ t = .nil := by
  constructor
  · intro h
    cases t with
    | nil => rfl
    | node k l r =>
      have hnum := numNodes_splayMax (t := .node k l r)
      rw [h] at hnum
      simp only [BinaryTree.numNodes] at hnum
      omega
  · rintro rfl
    rfl

private theorem splay_bounds_aux {α : Type u} [LinearOrder α] {x : α} (n : Nat)
    (t : BinaryTree α) (h : t.numNodes ≤ n) (hOrd : Ordered t) :
    ∀ {l : BinaryTree α} {a : α} {r : BinaryTree α},
    splay x t = .node a l r → All (· < x) l ∧ All (x < ·) r := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil =>
        intro l' a' r' hsp
        simp at hsp
      | node k l r =>
        simp only [BinaryTree.numNodes] at h
        omega
  | succ n ih =>
      cases t with
      | nil =>
        intro l' a' r' hsp
        simp at hsp
      | node k l r =>
        rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
        intro l' a' r' hsp
        by_cases hxk : x = k
        · subst hxk
          rw [splay_node_self rfl] at hsp
          obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
          exact ⟨hAllL, hAllR⟩
        · by_cases hlt : x < k
          · cases l with
            | nil =>
              rw [splay_node_left_nil hxk hlt] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
              exact ⟨trivial, all_mono (fun y hy => lt_trans hlt hy) hAllR⟩
            | node lk ll lr =>
              rcases hOrdL with ⟨hOrdLL, hOrdLR, hAllLL, hAllLR⟩
              by_cases hxl : x = lk
              · subst hxl
                rw [splay_zig_left hxk hlt rfl] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                exact ⟨hAllLL,
                  ⟨hAllLR, hlt, all_mono (fun y hy => lt_trans hlt hy) hAllR⟩⟩
              · by_cases hllt : x < lk
                · cases hs : splay x ll with
                  | nil =>
                    rw [splay_zigzig_left_nil hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hll : ll = .nil := splay_eq_nil.mp hs
                    subst hll
                    exact ⟨trivial,
                      ⟨all_mono (fun y hy => lt_trans hllt hy) hAllLR, hlt,
                        all_mono (fun y hy => lt_trans hlt hy) hAllR⟩⟩
                  | node d lll llr =>
                    rw [splay_zigzig_left_node hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : ll.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih ll hb hOrdLL hs
                    exact ⟨h1, h2, hllt,
                      ⟨all_mono (fun y hy => lt_trans hllt hy) hAllLR, hlt,
                        all_mono (fun y hy => lt_trans hlt hy) hAllR⟩⟩
                · have hgt : lk < x :=
                    lt_of_le_of_ne (le_of_not_gt hllt) (fun hh => hxl hh.symm)
                  cases hs : splay x lr with
                  | nil =>
                    rw [splay_zigzag_left_nil hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hlr : lr = .nil := splay_eq_nil.mp hs
                    subst hlr
                    exact ⟨all_mono (fun y hy => lt_trans hy hgt) hAllLL,
                      ⟨trivial, hlt, all_mono (fun y hy => lt_trans hlt hy) hAllR⟩⟩
                  | node d lrl lrr =>
                    rw [splay_zigzag_left_node hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : lr.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih lr hb hOrdLR hs
                    exact ⟨⟨all_mono (fun y hy => lt_trans hy hgt) hAllLL, hgt, h1⟩,
                      ⟨h2, hlt, all_mono (fun y hy => lt_trans hlt hy) hAllR⟩⟩
          · have hgt : k < x :=
              lt_of_le_of_ne (le_of_not_gt hlt) (fun hh => hxk hh.symm)
            cases r with
            | nil =>
              rw [splay_node_right_nil hxk hlt] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
              exact ⟨all_mono (fun y hy => lt_trans hy hgt) hAllL, trivial⟩
            | node rk rl rr =>
              rcases hOrdR with ⟨hOrdRL, hOrdRR, hAllRL, hAllRR⟩
              by_cases hxr : x = rk
              · subst hxr
                rw [splay_zig_right hxk hlt rfl] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                exact ⟨⟨all_mono (fun y hy => lt_trans hy hgt) hAllL, hgt, hAllRL⟩,
                  hAllRR⟩
              · by_cases hrrt : rk < x
                · cases hs : splay x rr with
                  | nil =>
                    rw [splay_zigzig_right_nil hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hrr : rr = .nil := splay_eq_nil.mp hs
                    subst hrr
                    exact ⟨⟨all_mono (fun y hy => lt_trans hy hgt) hAllL, hgt,
                      all_mono (fun y hy => lt_trans hy hrrt) hAllRL⟩, trivial⟩
                  | node d rrl rrr =>
                    rw [splay_zigzig_right_node hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : rr.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih rr hb hOrdRR hs
                    exact ⟨⟨⟨all_mono (fun y hy => lt_trans hy hgt) hAllL, hgt,
                      all_mono (fun y hy => lt_trans hy hrrt) hAllRL⟩, hrrt, h1⟩, h2⟩
                · have hxlt : x < rk := lt_of_le_of_ne (le_of_not_gt hrrt) hxr
                  cases hs : splay x rl with
                  | nil =>
                    rw [splay_zigzag_right_nil hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hrl : rl = .nil := splay_eq_nil.mp hs
                    subst hrl
                    exact ⟨⟨all_mono (fun y hy => lt_trans hy hgt) hAllL, hgt, trivial⟩,
                      all_mono (fun y hy => lt_trans hxlt hy) hAllRR⟩
                  | node d rll rlr =>
                    rw [splay_zigzag_right_node hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : rl.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih rl hb hOrdRL hs
                    exact ⟨⟨all_mono (fun y hy => lt_trans hy hgt) hAllL, hgt, h1⟩,
                      ⟨h2, hxlt, all_mono (fun y hy => lt_trans hxlt hy) hAllRR⟩⟩

/-- **Splay bounds.** In an ordered tree, every key in the left subtree
of `splay x t` is `< x` and every key in the right subtree is `> x`.
This is the crux lemma from which the `splayMax` and insertion
correctness arguments follow. -/
public theorem splay_bounds {α : Type u} [LinearOrder α] {x : α} {t : BinaryTree α}
    {l : BinaryTree α} {a : α} {r : BinaryTree α} (hOrd : Ordered t)
    (hsp : splay x t = .node a l r) : All (· < x) l ∧ All (x < ·) r :=
  splay_bounds_aux t.numNodes t (by omega) hOrd hsp

private theorem splayMax_eq_node_aux {α : Type u} (n : Nat) (t : BinaryTree α)
    (h : t.numNodes ≤ n) :
    ∀ {l : BinaryTree α} {a : α} {r : BinaryTree α},
    splayMax t = .node a l r → r = .nil ∧ inorder l ++ [a] = inorder t := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil =>
        intro l' a' r' hsp
        simp at hsp
      | node k l r =>
        simp only [BinaryTree.numNodes] at h
        omega
  | succ n ih =>
      cases t with
      | nil =>
        intro l' a' r' hsp
        simp at hsp
      | node k l r =>
        cases r with
        | nil =>
          intro l' a' r' hsp
          rw [show splayMax (.node k l .nil) = .node k l .nil from rfl] at hsp
          obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
          refine ⟨rfl, ?_⟩
          simp [inorder_node]
        | node rk rl rr =>
          cases hs : splayMax rr with
          | nil =>
            intro l' a' r' hsp
            rw [splayMax_node_node_of_nil hs] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
            have hrr : rr = .nil := splayMax_eq_nil.mp hs
            subst hrr
            refine ⟨rfl, ?_⟩
            simp [inorder_node, List.append_assoc]
          | node c C D =>
            intro l' a' r' hsp
            rw [splayMax_node_node_of_node hs] at hsp
            obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
            have hb : rr.numNodes ≤ n := by
              simp only [BinaryTree.numNodes] at h
              omega
            obtain ⟨hD, hIrr⟩ := ih rr hb hs
            refine ⟨hD, ?_⟩
            simp [inorder_node, List.append_assoc, hIrr]

/-- **Characterisation of `splayMax`.** If `splayMax t` is a node, its
right subtree is empty and its inorder traversal is `inorder l ++ [a]`,
so the root `a` is the maximum key of `t` for an ordered tree. -/
public theorem splayMax_eq_node {α : Type u} {t : BinaryTree α} {l : BinaryTree α}
    {a : α} {r : BinaryTree α} (h : splayMax t = .node a l r) :
    r = .nil ∧ inorder l ++ [a] = inorder t :=
  splayMax_eq_node_aux t.numNodes t (by omega) h

private theorem splay_max_eq_splay_aux {α : Type u} [LinearOrder α] {a : α} (n : Nat)
    (t : BinaryTree α) (h : t.numNodes ≤ n) (hOrd : Ordered t)
    (hbound : ∀ y ∈ t, y ≤ a) : splayMax t = splay a t := by
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
        rcases hOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
        cases r with
        | nil =>
          by_cases hak : a = k
          · subst hak
            have h0 : splayMax (.node a l .nil) = .node a l .nil := by simp [splayMax]
            rw [h0, splay_node_self rfl]
          · have hka : k < a :=
              lt_of_le_of_ne (hbound k (Or.inr (Or.inl rfl))) (Ne.symm hak)
            have h0 : splayMax (.node k l .nil) = .node k l .nil := by simp [splayMax]
            rw [h0, splay_node_right_nil hak (not_lt.mpr (le_of_lt hka))]
        | node rk rl rr =>
          rcases hOrdR with ⟨hOrdRL, hOrdRR, hAllRL, hAllRR⟩
          have hka : k < a :=
            lt_of_lt_of_le ((all_iff_forall_mem.mp hAllR) rk (Or.inr (Or.inl rfl)))
              (hbound rk (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          by_cases hxr : a = rk
          · subst hxr
            cases rr with
            | nil =>
              rw [splay_zig_right (Ne.symm (ne_of_lt hka)) (not_lt.mpr (le_of_lt hka)) rfl,
                splayMax_node_node_of_nil rfl]
            | node c C D =>
              exfalso
              have hcle : c ≤ a :=
                hbound c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
              have hac : a < c :=
                (all_iff_forall_mem.mp hAllRR) c (Or.inr (Or.inl rfl))
              exact absurd hcle (not_le_of_gt hac)
          · by_cases hrac : rk < a
            · cases hs : splay a rr with
              | nil =>
                have hsMax : splayMax rr = .nil :=
                  splayMax_eq_nil.mpr (splay_eq_nil.mp hs)
                rw [splay_zigzig_right_nil (Ne.symm (ne_of_lt hka)) (not_lt.mpr (le_of_lt hka))
                  hxr hrac hs, splayMax_node_node_of_nil hsMax]
                have hrr0 : rr = .nil := splay_eq_nil.mp hs
                rw [hrr0]
              | node d rrl rrr =>
                have hb : rr.numNodes ≤ n := by
                  simp only [BinaryTree.numNodes] at h
                  omega
                have hbound_rr : ∀ y ∈ rr, y ≤ a :=
                  fun y hy => hbound y (Or.inr (Or.inr (Or.inr (Or.inr hy))))
                have hs' : splayMax rr = .node d rrl rrr :=
                  (ih rr hb hOrdRR hbound_rr).trans hs
                rw [splay_zigzig_right_node (Ne.symm (ne_of_lt hka)) (not_lt.mpr (le_of_lt hka))
                  hxr hrac hs, splayMax_node_node_of_node hs']
            · have har : a < rk := lt_of_le_of_ne (le_of_not_gt hrac) hxr
              exact absurd (hbound rk (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (not_le_of_gt har)

/-- **Splaying the maximum equals splaying a key above all keys.**
For an ordered tree and a key `a` at least every key of `t`,
`splayMax t = splay a t`. -/
public theorem splay_max_eq_splay {α : Type u} [LinearOrder α] {a : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hbound : ∀ y ∈ t, y ≤ a) :
    splayMax t = splay a t :=
  splay_max_eq_splay_aux t.numNodes t (by omega) hOrd hbound

/-- **Some key splays to `splayMax`.** For a nonempty ordered tree,
the maximum key splays to `splayMax t`; the empty tree is handled by
any key. -/
public theorem splay_max_eq_splay_ex {α : Type u} [LinearOrder α] [Nonempty α]
    {t : BinaryTree α} (hOrd : Ordered t) : ∃ a, splayMax t = splay a t := by
  cases t with
  | nil => exact ⟨Classical.arbitrary α, rfl⟩
  | node k l r =>
    cases hsp : splayMax (.node k l r) with
    | nil => exact absurd hsp (splayMax_ne_nil (by simp))
    | node a' l' r' =>
      obtain ⟨hr', hin⟩ := splayMax_eq_node hsp
      refine ⟨a', ?_⟩
      have hEq : splayMax (.node k l r) = splay a' (.node k l r) :=
        splay_max_eq_splay (t := .node k l r) hOrd ?_
      · rw [hsp] at hEq
        exact hEq
      · intro y hy
        have hmem : y ∈ inorder (.node k l r) := mem_inorder.mpr hy
        rw [← hin] at hmem
        rw [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hyl | rfl
        · have hpair := ordered_inorder hOrd
          rw [← hin] at hpair
          rw [List.pairwise_append] at hpair
          obtain ⟨_, _, hmid⟩ := hpair
          exact le_of_lt (hmid y hyl a' (List.mem_singleton_self a'))
        · exact le_rfl

/--
Delete a key by splaying (Nipkow's `delete`, FDSA §21.1): splay `x`
to the root; if it is there, replace it by the maximum of the left
subtree, splayed to the root of that subtree, with the right subtree
attached. If `x` is absent the splayed tree is returned unchanged.
-/
public def delete {α : Type u} [LinearOrder α] (x : α) (t : BinaryTree α) : BinaryTree α :=
  match splay x t with
  | .nil => .nil
  | .node a l r =>
    if x = a then
      match splayMax l with
      | .node m l' _ => .node m l' r
      | .nil => r
    else .node a l r

/-- Deleting an absent key returns the splayed tree unchanged. -/
public theorem delete_eq_of_ne {α : Type u} [LinearOrder α] {x a : α}
    {t l r : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : x ≠ a) :
    delete x t = .node a l r := by
  unfold delete
  rw [hsp]
  simp [hxa]

/-- Deleting a present key with an empty left subtree returns the right subtree. -/
public theorem delete_eq_of_eq_nil {α : Type u} [LinearOrder α] {x a : α}
    {t l r : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : x = a)
    (hmax : splayMax l = .nil) : delete x t = r := by
  unfold delete
  rw [hsp]
  simp [hxa, hmax]

/-- Deleting a present key replaces it by the maximum of the left subtree. -/
public theorem delete_eq_of_eq_node {α : Type u} [LinearOrder α] {x a m : α}
    {t l r l' D : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : x = a)
    (hmax : splayMax l = .node m l' D) : delete x t = .node m l' r := by
  unfold delete
  rw [hsp]
  simp [hxa, hmax]

/-- Deleting a key removes exactly that key from structural membership. -/
public theorem mem_delete {α : Type u} [LinearOrder α] {x y : α} {t : BinaryTree α}
    (hOrd : Ordered t) : y ∈ delete x t ↔ y ∈ t ∧ y ≠ x := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    simp [delete, hs]
  | node a l r =>
    have hsOrd : Ordered (.node a l r) := by
      rw [← hs]
      exact ordered_splay hOrd
    by_cases hxa : x = a
    · cases hmax : splayMax l with
      | nil =>
        have hl : l = .nil := splayMax_eq_nil.mp hmax
        subst hl
        rw [delete_eq_of_eq_nil hs hxa hmax]
        rcases hsOrd with ⟨_, _, _, hAllR⟩
        constructor
        · intro hy
          refine ⟨mem_splay.mp (by rw [hs]; exact Or.inr (Or.inr hy)), ?_⟩
          have hay : a < y := (all_iff_forall_mem.mp hAllR) y hy
          exact fun h => ne_of_gt hay (h.trans hxa)
        · rintro ⟨hy, hyx⟩
          have hyt : y ∈ BinaryTree.node a .nil r := by
            have h1 : y ∈ splay x t := mem_splay.mpr hy
            rwa [hs] at h1
          rcases hyt with hy | hya | hyr
          · exact False.elim hy
          · exact absurd (hya.trans hxa.symm) hyx
          · exact hyr
      | node m l' D =>
        rw [delete_eq_of_eq_node hs hxa hmax]
        obtain ⟨hD, _⟩ := splayMax_eq_node hmax
        have hmem_l : ∀ z, z ∈ l ↔ z ∈ l' ∨ z = m := by
          intro z
          rw [← mem_splayMax, hmax]
          simp [hD]
        rcases hsOrd with ⟨hOrdL, _, hAllL, hAllR⟩
        constructor
        · intro hy
          rcases hy with hy | hye | hy
          · have hyl : y ∈ l := (hmem_l y).mpr (Or.inl hy)
            refine ⟨mem_splay.mp (by rw [hs]; exact Or.inl hyl), ?_⟩
            have hya : y < a := (all_iff_forall_mem.mp hAllL) y hyl
            exact fun h => ne_of_lt hya (h.trans hxa)
          · have hml : m ∈ l := (hmem_l m).mpr (Or.inr rfl)
            have hma : m < a := (all_iff_forall_mem.mp hAllL) m hml
            refine ⟨mem_splay.mp (by rw [hs]; exact Or.inl (hye.symm ▸ hml)), ?_⟩
            exact fun h => ne_of_lt (hye.symm ▸ hma) (h.trans hxa)
          · refine ⟨mem_splay.mp (by rw [hs]; exact Or.inr (Or.inr hy)), ?_⟩
            have hay : a < y := (all_iff_forall_mem.mp hAllR) y hy
            exact fun h => ne_of_gt hay (h.trans hxa)
        · rintro ⟨hy, hyx⟩
          have hyt : y ∈ BinaryTree.node a l r := by
            have h1 : y ∈ splay x t := mem_splay.mpr hy
            rwa [hs] at h1
          rcases hyt with hyl | hya | hyr
          · rcases (hmem_l y).mp hyl with hy' | hy'
            · exact Or.inl hy'
            · exact Or.inr (Or.inl hy')
          · exact absurd (hya.trans hxa.symm) hyx
          · exact Or.inr (Or.inr hyr)
    · rw [delete_eq_of_ne hs hxa]
      have hxnot : x ∉ t := by
        intro hx
        obtain ⟨l1, r1, hsp1⟩ := root_splay_of_mem hOrd hx
        rw [hs] at hsp1
        obtain ⟨h1, -, -⟩ := BinaryTree.node.inj hsp1
        exact hxa h1.symm
      constructor
      · intro hy
        refine ⟨mem_splay.mp (by rwa [hs]), ?_⟩
        intro hyx
        exact hxnot (hyx ▸ mem_splay.mp (by rwa [hs]))
      · rintro ⟨hy, -⟩
        have h1 : y ∈ splay x t := mem_splay.mpr hy
        rwa [hs] at h1

/-- Deletion preserves the strict search-tree invariant. -/
public theorem ordered_delete {α : Type u} [LinearOrder α] {x : α} {t : BinaryTree α}
    (hOrd : Ordered t) : Ordered (delete x t) := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    exact trivial
  | node a l r =>
    have hsOrd : Ordered (.node a l r) := by
      rw [← hs]
      exact ordered_splay hOrd
    by_cases hxa : x = a
    · subst hxa
      cases hmax : splayMax l with
      | nil =>
        rw [delete_eq_of_eq_nil hs rfl hmax]
        exact hsOrd.2.1
      | node m l' D =>
        rw [delete_eq_of_eq_node hs rfl hmax]
        rcases hsOrd with ⟨hOrdL, hOrdR, hAllL, hAllR⟩
        have hsOrdMax : Ordered (.node m l' D) := hmax ▸ ordered_splayMax hOrdL
        rcases hsOrdMax with ⟨hOrdL', _, hAllL', _⟩
        refine ⟨hOrdL', hOrdR, hAllL', ?_⟩
        have hml : m ∈ l := by
          have hm : m ∈ splayMax l := by rw [hmax]; exact Or.inr (Or.inl rfl)
          exact mem_splayMax.mp hm
        have hma : m < x := (all_iff_forall_mem.mp hAllL) m hml
        exact all_mono (fun y hy => lt_trans hma hy) hAllR
    · rw [delete_eq_of_ne hs hxa]
      exact hsOrd

/-- Deleting a key filters it out of the inorder traversal. -/
public theorem inorder_delete {α : Type u} [LinearOrder α] {x : α} {t : BinaryTree α}
    (hOrd : Ordered t) :
    inorder (delete x t) = (inorder t).filter (· ≠ x) := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    simp [delete, hs]
  | node a l r =>
    have hsOrd : Ordered (.node a l r) := by
      rw [← hs]
      exact ordered_splay hOrd
    by_cases hxa : x = a
    · subst hxa
      cases hmax : splayMax l with
      | nil =>
        have hl : l = .nil := splayMax_eq_nil.mp hmax
        subst hl
        rw [delete_eq_of_eq_nil hs rfl hmax]
        rcases hsOrd with ⟨_, _, _, hAllR⟩
        have h1 : inorder (.node x .nil r) = [x] ++ inorder r := by
          simp [inorder_node]
        have h2 : ([x] ++ inorder r).filter (· ≠ x) = inorder r := by
          rw [List.filter_append]
          have hfa : ([x] : List α).filter (· ≠ x) = [] := by simp
          rw [hfa, List.nil_append]
          apply List.filter_eq_self.mpr
          intro y hy
          have hyr : y ∈ r := mem_inorder.mp hy
          have hay : x < y := (all_iff_forall_mem.mp hAllR) y hyr
          exact decide_eq_true_eq.mpr (ne_of_gt hay)
        have ht : inorder t = [x] ++ inorder r := by
          rw [← inorder_splay (x := x) (t := t), hs]
          exact h1
        rw [ht, h2]
      | node m l' D =>
        rw [delete_eq_of_eq_node hs rfl hmax]
        obtain ⟨_, hin⟩ := splayMax_eq_node hmax
        rcases hsOrd with ⟨_, _, hAllL, hAllR⟩
        have h1 : inorder t = inorder l ++ [x] ++ inorder r := by
          rw [← inorder_splay (x := x) (t := t), hs]
          simp [inorder_node, List.append_assoc]
        have h2 : (inorder l ++ [x] ++ inorder r).filter (· ≠ x) =
            inorder l ++ inorder r := by
          have hfl : (inorder l).filter (· ≠ x) = inorder l := by
            apply List.filter_eq_self.mpr
            intro y hy
            have hyl : y ∈ l := mem_inorder.mp hy
            have hya : y < x := (all_iff_forall_mem.mp hAllL) y hyl
            exact decide_eq_true_eq.mpr (ne_of_lt hya)
          have hfa : ([x] : List α).filter (· ≠ x) = [] := by simp
          have hfr : (inorder r).filter (· ≠ x) = inorder r := by
            apply List.filter_eq_self.mpr
            intro y hy
            have hyr : y ∈ r := mem_inorder.mp hy
            have hay : x < y := (all_iff_forall_mem.mp hAllR) y hyr
            exact decide_eq_true_eq.mpr (ne_of_gt hay)
          rw [List.filter_append, List.filter_append, hfl, hfa, hfr]
          simp
        have hin' : inorder l' ++ m :: inorder r = inorder l ++ inorder r := by
          rw [← hin]
          simp [List.append_assoc]
        rw [h1, h2, inorder_node]
        exact hin'
    · rw [delete_eq_of_ne hs hxa]
      have hxnot : x ∉ t := by
        intro hx
        obtain ⟨l1, r1, hsp1⟩ := root_splay_of_mem hOrd hx
        rw [hs] at hsp1
        obtain ⟨h1, -, -⟩ := BinaryTree.node.inj hsp1
        exact hxa h1.symm
      rw [← inorder_splay (x := x) (t := t), hs]
      symm
      apply List.filter_eq_self.mpr
      intro y hy
      have hyt : y ∈ t := by
        have h1 : y ∈ splay x t := by
          rw [hs]
          exact mem_inorder.mp hy
        exact mem_splay.mp h1
      exact decide_eq_true_eq.mpr (fun hyx => hxnot (hyx ▸ hyt))

/-- Deleting a present key decreases the number of nodes by one. -/
public theorem numNodes_delete_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    (delete x t).numNodes = t.numNodes - 1 := by
  obtain ⟨l, r, hsp⟩ := root_splay_of_mem hOrd hx
  have hnum1 := numNodes_splay (x := x) (t := t)
  rw [hsp] at hnum1
  cases hmax : splayMax l with
  | nil =>
    have hl : l = .nil := splayMax_eq_nil.mp hmax
    subst hl
    rw [delete_eq_of_eq_nil hsp rfl hmax]
    simp only [BinaryTree.numNodes] at hnum1
    omega
  | node m l' D =>
    have hnum2 := numNodes_splayMax (t := l)
    rw [hmax] at hnum2
    obtain ⟨hD, -⟩ := splayMax_eq_node hmax
    subst hD
    rw [delete_eq_of_eq_node hsp rfl hmax]
    simp only [BinaryTree.numNodes] at hnum1 hnum2 ⊢
    omega

/-- Deleting an absent key leaves the number of nodes unchanged. -/
public theorem numNodes_delete_of_not_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∉ t) :
    (delete x t).numNodes = t.numNodes := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    simp [delete, hs]
  | node a l r =>
    by_cases hxa : x = a
    · exfalso
      exact hx (mem_splay.mp (by rw [hs, ← hxa]; exact Or.inr (Or.inl rfl)))
    · rw [delete_eq_of_ne hs hxa]
      have hnum := numNodes_splay (x := x) (t := t)
      rwa [hs] at hnum

/--
Insert a key by splaying (Nipkow's `insert`, FDSA §21.1): splay `x` to the root;
if it is there the tree is unchanged, otherwise `x` becomes the new root with the
splayed tree split around it. This is the book's formulation (splay, then rebuild
around the new root). It computes the same tree as `SplayTree.insert`
(`insert_eq_nipkowInsert`), which applies `split` to the splayed tree instead;
`costInsert` in `CSLibExt.Algorithms.Lean.DataStructures.SplayTree.Amortized`
charges the book's splay-then-rebuild.
-/
public def nipkowInsert {α : Type u} [LinearOrder α] (x : α) (t : BinaryTree α) : BinaryTree α :=
  match splay x t with
  | .nil => .node x .nil .nil
  | .node a l r =>
      if x = a then .node a l r
      else if x < a then .node x l (.node a .nil r)
      else .node x (.node a l .nil) r

/-- Inserting into the empty tree creates a singleton. -/
public theorem nipkowInsert_eq_of_nil {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hsp : splay x t = .nil) :
    nipkowInsert x t = .node x .nil .nil := by
  unfold nipkowInsert
  rw [hsp]

/-- Inserting a present key returns the splayed tree unchanged. -/
public theorem nipkowInsert_eq_of_eq {α : Type u} [LinearOrder α] {x a : α}
    {t l r : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : x = a) :
    nipkowInsert x t = .node a l r := by
  unfold nipkowInsert
  rw [hsp]
  simp [hxa]

/-- Inserting a smaller key makes it the new root, with the old tree on the right. -/
public theorem nipkowInsert_eq_of_lt {α : Type u} [LinearOrder α] {x a : α}
    {t l r : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : x < a) :
    nipkowInsert x t = .node x l (.node a .nil r) := by
  unfold nipkowInsert
  rw [hsp]
  simp [ne_of_lt hxa, hxa]

/-- Inserting a larger key makes it the new root, with the old tree on the left. -/
public theorem nipkowInsert_eq_of_gt {α : Type u} [LinearOrder α] {x a : α}
    {t l r : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : a < x) :
    nipkowInsert x t = .node x (.node a l .nil) r := by
  unfold nipkowInsert
  rw [hsp]
  simp [ne_of_gt hxa, not_lt.mpr (le_of_lt hxa)]

private theorem split_of_splay_eq_node_aux {α : Type u} [LinearOrder α] {x : α} (n : Nat)
    (t : BinaryTree α) (h : t.numNodes ≤ n) :
    ∀ {l : BinaryTree α} {a : α} {r : BinaryTree α}, splay x t = .node a l r →
      (x < a → split x l = (l, .nil)) ∧ (a < x → split x r = (.nil, r)) := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil =>
        intro l' a' r' hsp
        simp at hsp
      | node k l r =>
        simp only [BinaryTree.numNodes] at h
        omega
  | succ n ih =>
      cases t with
      | nil =>
        intro l' a' r' hsp
        simp at hsp
      | node k l r =>
        intro l' a' r' hsp
        by_cases hxk : x = k
        · subst hxk
          rw [splay_node_self rfl] at hsp
          obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
          exact ⟨fun hx => absurd hx (lt_irrefl _), fun hx => absurd hx (lt_irrefl _)⟩
        · by_cases hlt : x < k
          · cases l with
            | nil =>
              rw [splay_node_left_nil hxk hlt] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
              exact ⟨fun _ => rfl, fun hkx => absurd hlt (lt_asymm hkx)⟩
            | node lk ll lr =>
              by_cases hxl : x = lk
              · subst hxl
                rw [splay_zig_left hxk hlt rfl] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                exact ⟨fun hx => absurd hx (lt_irrefl _), fun hx => absurd hx (lt_irrefl _)⟩
              · by_cases hllt : x < lk
                · cases hs : splay x ll with
                  | nil =>
                    rw [splay_zigzig_left_nil hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hll : ll = .nil := splay_eq_nil.mp hs
                    subst hll
                    exact ⟨fun _ => rfl, fun hkx => absurd hllt (lt_asymm hkx)⟩
                  | node d lll llr =>
                    rw [splay_zigzig_left_node hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : ll.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih ll hb hs
                    exact ⟨h1, fun hdx => by rw [split_node_lt hllt, h2 hdx]⟩
                · have hgt : lk < x :=
                    lt_of_le_of_ne (le_of_not_gt hllt) (fun hh => hxl hh.symm)
                  cases hs : splay x lr with
                  | nil =>
                    rw [splay_zigzag_left_nil hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hlr : lr = .nil := splay_eq_nil.mp hs
                    subst hlr
                    exact ⟨fun hxl' => absurd hgt (lt_asymm hxl'), fun _ => split_node_lt hlt⟩
                  | node d lrl lrr =>
                    rw [splay_zigzag_left_node hxk hlt hxl hllt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : lr.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih lr hb hs
                    exact ⟨fun hxd => by rw [split_node_gt hllt hgt, h1 hxd],
                      fun hdx => by rw [split_node_lt hlt, h2 hdx]⟩
          · have hgt : k < x :=
              lt_of_le_of_ne (le_of_not_gt hlt) (fun hh => hxk hh.symm)
            cases r with
            | nil =>
              rw [splay_node_right_nil hxk hlt] at hsp
              obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
              exact ⟨fun hxk' => absurd hxk' hlt, fun _ => rfl⟩
            | node rk rl rr =>
              by_cases hxr : x = rk
              · subst hxr
                rw [splay_zig_right hxk hlt rfl] at hsp
                obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                exact ⟨fun hx => absurd hx (lt_irrefl _), fun hx => absurd hx (lt_irrefl _)⟩
              · by_cases hrrt : rk < x
                · cases hs : splay x rr with
                  | nil =>
                    rw [splay_zigzig_right_nil hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hrr : rr = .nil := splay_eq_nil.mp hs
                    subst hrr
                    exact ⟨fun hxr' => absurd hrrt (lt_asymm hxr'), fun _ => rfl⟩
                  | node d rrl rrr =>
                    rw [splay_zigzig_right_node hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : rr.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih rr hb hs
                    exact ⟨fun hxd => by rw [split_node_gt (lt_asymm hrrt) hrrt, h1 hxd], h2⟩
                · have hxlt : x < rk := lt_of_le_of_ne (le_of_not_gt hrrt) hxr
                  cases hs : splay x rl with
                  | nil =>
                    rw [splay_zigzag_right_nil hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hrl : rl = .nil := splay_eq_nil.mp hs
                    subst hrl
                    exact ⟨fun _ => split_node_gt hlt hgt,
                      fun hrx => absurd hxlt (lt_asymm hrx)⟩
                  | node d rll rlr =>
                    rw [splay_zigzag_right_node hxk hlt hxr hrrt hs] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := BinaryTree.node.inj hsp
                    have hb : rl.numNodes ≤ n := by
                      simp only [BinaryTree.numNodes] at h
                      omega
                    obtain ⟨h1, h2⟩ := ih rl hb hs
                    exact ⟨fun hxd => by rw [split_node_gt hlt hgt, h1 hxd],
                      fun hdx => by rw [split_node_lt hxlt, h2 hdx]⟩

/-- **Splay-tree insertion and the book's insertion agree.** For every key $x$ and every binary
tree $t$ over a linearly ordered type, the splay-tree insertion of $x$ into $t$ (splay, then
split) and the book's insertion of $x$ into $t$ (splay, then rebuild around the new root; Nipkow,
FDSA §21.1) are the same tree, whether or not $t$ is a binary search tree. Suppose that splaying
$x$ in $t$ gives the tree with root key $a$, left subtree $L$ and right subtree $R$. If $x < a$,
the search for $x$ turned right at every node of the right spine of $L$, so every key on that
spine is smaller than $x$; splitting the splayed tree at $x$ thus gives $L$ and the tree with
root key $a$, empty left subtree and right subtree $R$, which are the two subtrees that the book
puts under the new root $x$. The case $a < x$ is the mirror image, and the cases $x = a$ and $t$
empty are immediate. -/
public theorem insert_eq_nipkowInsert {α : Type u} [LinearOrder α] (x : α) (t : BinaryTree α) :
    insert x t = nipkowInsert x t := by
  rw [insert_eq]
  cases hs : splay x t with
  | nil =>
    rw [nipkowInsert_eq_of_nil hs]
    rfl
  | node a l r =>
    obtain ⟨hl, hr⟩ := split_of_splay_eq_node_aux t.numNodes t (by omega) hs
    rcases lt_trichotomy x a with hxa | rfl | hxa
    · rw [nipkowInsert_eq_of_lt hs hxa, split_node_lt hxa, hl hxa]
    · rw [nipkowInsert_eq_of_eq hs rfl, split_node_eq (lt_irrefl _) (lt_irrefl _)]
    · rw [nipkowInsert_eq_of_gt hs hxa, split_node_gt (lt_asymm hxa) hxa, hr hxa]

/-- Inserting a key adds exactly that key to structural membership. -/
public theorem mem_nipkowInsert {α : Type u} [LinearOrder α] {x y : α} {t : BinaryTree α}
    (hOrd : Ordered t) : y ∈ nipkowInsert x t ↔ y ∈ t ∨ y = x := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    rw [nipkowInsert_eq_of_nil hs]
    constructor
    · intro hy
      rcases hy with hy | rfl | hy
      · exact False.elim hy
      · exact Or.inr rfl
      · exact False.elim hy
    · rintro (hy | rfl)
      · exact False.elim hy
      · exact Or.inr (Or.inl rfl)
  | node a l r =>
    obtain ⟨hbl, hbr⟩ := splay_bounds hOrd hs
    rcases lt_trichotomy x a with hxa | hxa | hxa
    · rw [nipkowInsert_eq_of_lt hs hxa]
      constructor
      · intro hy
        rcases hy with hy | rfl | hy
        · exact Or.inl (mem_splay.mp (by rw [hs]; exact Or.inl hy))
        · exact Or.inr rfl
        · rcases hy with hy | rfl | hy
          · exact False.elim hy
          · exact Or.inl (mem_splay.mp (by rw [hs]; exact Or.inr (Or.inl rfl)))
          · exact Or.inl (mem_splay.mp (by rw [hs]; exact Or.inr (Or.inr hy)))
      · rintro (hy | rfl)
        · have hyt : y ∈ BinaryTree.node a l r := by
            have h1 : y ∈ splay x t := mem_splay.mpr hy
            rwa [hs] at h1
          rcases hyt with hyl | hya | hyr
          · exact Or.inl hyl
          · exact Or.inr (Or.inr (Or.inr (Or.inl hya)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hyr)))
        · exact Or.inr (Or.inl rfl)
    · rw [nipkowInsert_eq_of_eq hs hxa]
      constructor
      · intro hy
        exact Or.inl (mem_splay.mp (by rw [hs]; exact hy))
      · rintro (hy | rfl)
        · have h1 : y ∈ splay x t := mem_splay.mpr hy
          rwa [hs] at h1
        · exact Or.inr (Or.inl hxa)
    · rw [nipkowInsert_eq_of_gt hs hxa]
      constructor
      · intro hy
        rcases hy with hy | rfl | hy
        · rcases hy with hy | rfl | hy
          · exact Or.inl (mem_splay.mp (by rw [hs]; exact Or.inl hy))
          · exact Or.inl (mem_splay.mp (by rw [hs]; exact Or.inr (Or.inl rfl)))
          · exact False.elim hy
        · exact Or.inr rfl
        · exact Or.inl (mem_splay.mp (by rw [hs]; exact Or.inr (Or.inr hy)))
      · rintro (hy | rfl)
        · have hyt : y ∈ BinaryTree.node a l r := by
            have h1 : y ∈ splay x t := mem_splay.mpr hy
            rwa [hs] at h1
          rcases hyt with hyl | hya | hyr
          · exact Or.inl (Or.inl hyl)
          · exact Or.inl (Or.inr (Or.inl hya))
          · exact Or.inr (Or.inr hyr)
        · exact Or.inr (Or.inl rfl)

/-- Insertion preserves the strict search-tree invariant. -/
public theorem ordered_nipkowInsert {α : Type u} [LinearOrder α] {x : α} {t : BinaryTree α}
    (hOrd : Ordered t) : Ordered (nipkowInsert x t) := by
  rw [← insert_eq_nipkowInsert]
  exact ordered_insert hOrd

/-- Inserting a present key leaves the number of nodes unchanged. -/
public theorem numNodes_nipkowInsert_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    (nipkowInsert x t).numNodes = t.numNodes := by
  obtain ⟨l, r, hsp⟩ := root_splay_of_mem hOrd hx
  rw [nipkowInsert_eq_of_eq hsp rfl]
  have hnum := numNodes_splay (x := x) (t := t)
  rwa [hsp] at hnum

/-- Inserting an absent key increases the number of nodes by one. -/
public theorem numNodes_nipkowInsert_of_not_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∉ t) :
    (nipkowInsert x t).numNodes = t.numNodes + 1 := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    rw [nipkowInsert_eq_of_nil hs]
    simp [BinaryTree.numNodes]
  | node a l r =>
    have hnum : (BinaryTree.node a l r).numNodes = t.numNodes := by
      rw [← hs]
      exact numNodes_splay
    rcases lt_trichotomy x a with hxa | hxa | hxa
    · rw [nipkowInsert_eq_of_lt hs hxa]
      simp only [BinaryTree.numNodes] at hnum ⊢
      omega
    · exfalso
      exact hx (mem_splay.mp (by rw [hs]; exact Or.inr (Or.inl hxa)))
    · rw [nipkowInsert_eq_of_gt hs hxa]
      simp only [BinaryTree.numNodes] at hnum ⊢
      omega

/-- Inserting a present key leaves the inorder traversal unchanged. -/
public theorem inorder_nipkowInsert_of_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∈ t) :
    inorder (nipkowInsert x t) = inorder t := by
  obtain ⟨l, r, hsp⟩ := root_splay_of_mem hOrd hx
  rw [nipkowInsert_eq_of_eq hsp rfl, ← hsp]
  exact inorder_splay (x := x) (t := t)

/-- Inserting an absent key splices it into the inorder traversal at its sorted position. -/
public theorem inorder_nipkowInsert_of_not_mem {α : Type u} [LinearOrder α] {x : α}
    {t : BinaryTree α} (hOrd : Ordered t) (hx : x ∉ t) :
    ∃ l' r', inorder t = l' ++ r' ∧ inorder (nipkowInsert x t) = l' ++ [x] ++ r' ∧
      (∀ y ∈ l', y < x) ∧ (∀ y ∈ r', x < y) := by
  cases hs : splay x t with
  | nil =>
    have ht : t = .nil := splay_eq_nil.mp hs
    subst ht
    refine ⟨[], [], by simp, ?_, fun _ h => by simp at h, fun _ h => by simp at h⟩
    rw [nipkowInsert_eq_of_nil hs]
    simp [BinarySearchTree.inorder, BinarySearchTree.inorderAux]
  | node a l r =>
    obtain ⟨hbl, hbr⟩ := splay_bounds hOrd hs
    have hin_t : inorder t = inorder l ++ [a] ++ inorder r := by
      rw [← inorder_splay (x := x) (t := t), hs]
      simp [inorder_node, List.append_assoc]
    rcases lt_trichotomy x a with hxa | hxa | hxa
    · refine ⟨inorder l, [a] ++ inorder r, by rw [hin_t, List.append_assoc], ?_, ?_, ?_⟩
      · rw [nipkowInsert_eq_of_lt hs hxa]
        simp [inorder_node, List.append_assoc]
      · intro y hy
        exact (all_iff_forall_mem.mp hbl) y (mem_inorder.mp hy)
      · intro y hy
        rw [List.mem_append, List.mem_singleton] at hy
        rcases hy with rfl | hy
        · exact hxa
        · exact (all_iff_forall_mem.mp hbr) y (mem_inorder.mp hy)
    · exfalso
      exact hx (mem_splay.mp (by rw [hs]; exact Or.inr (Or.inl hxa)))
    · refine ⟨inorder l ++ [a], inorder r, ?_, ?_, ?_, ?_⟩
      · rw [hin_t]
      · rw [nipkowInsert_eq_of_gt hs hxa]
        simp [inorder_node, List.append_assoc]
      · intro y hy
        rw [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact (all_iff_forall_mem.mp hbl) y (mem_inorder.mp hy)
        · exact hxa
      · intro y hy
        exact (all_iff_forall_mem.mp hbr) y (mem_inorder.mp hy)

end SplayTree
end Cslib.Algorithms.Lean
