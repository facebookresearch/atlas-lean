/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SplayTree
public import CSLibExt.Algorithms.Lean.DataStructures.PotentialMethod
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Amortized analysis of splaying: the access lemma

Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985) 652–686, §2.

**Cost model.** The cost of `splay x t` is the number of rotations it performs, or one if it
performs none (Sleator–Tarjan, §2: "As a measure of the running time of a splaying operation,
we use the number of rotations done, unless there are no rotations, in which case we charge one
for the splaying"). A zig-zig or zig-zag step counts two rotations, a zig step one.

**Potential.** Each item `i` has a positive weight `w(i)`; the size of a node is the total
weight of its subtree (`weight`), its rank is `log₂` of that size, and the potential of a tree
is the sum of the ranks of its nodes (`potentialW`). With unit weights the size is the number of
nodes of the subtree (`potential`).

**Results.**
* `access_lemma_weighted`: for any positive weights, the amortized cost of splaying `t` at `x`
  is at most `3 (log₂ W(t) - log₂ W(focus x t)) + 1`, Lemma 1 (Access Lemma) of Sleator–Tarjan;
  for a present key of a search tree, at most `3 (log₂ W(t) - log₂ w(x)) + 1`
  (`amortized_cost_le_weighted`);
* `access_sequence_le_weighted`: the total cost of a sequence of accesses is at most
  `∑_j (3 log₂ (W / w(x_j)) + 1) + ∑_i log₂ (W / w(i))`, from which Sleator and Tarjan derive
  their Theorems 1–3 by choosing weights; `static_optimality` is Theorem 2 (Static Optimality);
* `access_lemma`: with unit weights, the amortized cost of splaying `t` at `x` is at most
  `3 (log₂ |t| - log₂ |focus x t|) + 1`, where `focus x t` is the subtree rooted at the last
  node of the search path for `x` (the node containing `x` when `x` is present). This is
  Lemma 1 (Access Lemma) of Sleator–Tarjan with unit weights.
* `amortized_cost_le`: hence the amortized cost of one splay on an `n`-node tree is at most
  `3 log₂ n + 1`.
* `balance_theorem`: any `m` successive splays starting from an `n`-node tree cost in total
  at most `m (3 log₂ n + 1) + n log₂ n`, the explicit form of Theorem 1 (Balance Theorem).
* `amortized_splayMax_le`: the amortized cost of `splayMax t` is at most `3 log₂ n + 1`
  in the repo's rotation-based cost model (the FDSA/AFP `A_splay_max` analogue; AFP
  states `3 * φ t + 1` with `φ t = log₂ (size1 t)`).
* `amortized_delete_le`: the amortized cost of `delete x t` is at most `5 log₂ n + 2`
  in the repo's rotation-based cost model (the FDSA/AFP `A_delete` analogue; AFP
  states `6 log₂ (size1 t) + 2`).
* `amortized_nipkowInsert_le`: the amortized cost of the book's `nipkowInsert x t`
  is at most `4 log₂ n + 2` in the repo's rotation-based cost model (the FDSA/AFP
  `A_insert` analogue; AFP states `4 log₂ (size1 t) + 2`). The tree is the same as
  `insert x t` (`insert_eq_nipkowInsert`); `costInsert` charges the book's
  splay-then-rebuild, not the `split` that `insert` performs instead.

**On the splaying variant.** `SplayTree.splay` is recursive and consumes two levels of the
search path per step starting from the root, so when the access depth is odd its single
rotation (zig) happens at the bottom of the path rather than at the root as in Sleator and
Tarjan's bottom-up splaying; the resulting tree can differ. The access-lemma argument applies
verbatim, since the bound for a zig step, `1 + 3 (r'(x) - r(x))`, holds wherever the step
occurs; `access_lemma_weighted` (hence `access_lemma`) proves this for the recursive
formulation.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace SplayTree

variable {α : Type u}

/-- **Splay-tree potential.** With unit weights, the potential of a binary tree is the sum over
its nodes of `log₂` of the number of nodes in the subtree rooted there (Sleator and Tarjan,
*Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2, with all weights equal to one). -/
noncomputable def potential : BinaryTree α → ℝ
  | .nil => 0
  | .node k l r =>
      potential l + potential r + Real.logb 2 ((BinaryTree.node k l r).numNodes : ℝ)

/-- **Number of rotations performed by splaying.** `rotations x t` counts the single rotations
performed by `SplayTree.splay x t`: one for a zig step and two for a zig-zig or zig-zag step
(Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2). -/
def rotations [LinearOrder α] (x : α) : BinaryTree α → ℕ
  | .nil => 0
  | .node k l r =>
      if x = k then 0
      else if x < k then
        match l with
        | .nil => 0
        | .node lk ll lr =>
            if x = lk then 1
            else if x < lk then
              match ll with
              | .nil => 1
              | .node _ _ _ => rotations x ll + 2
            else
              match lr with
              | .nil => 1
              | .node _ _ _ => rotations x lr + 2
      else
        match r with
        | .nil => 0
        | .node rk rl rr =>
            if x = rk then 1
            else if rk < x then
              match rr with
              | .nil => 1
              | .node _ _ _ => rotations x rr + 2
            else
              match rl with
              | .nil => 1
              | .node _ _ _ => rotations x rl + 2

/-- **Cost of a splay.** The number of rotations performed by `SplayTree.splay x t`, or one if
there are none (Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985),
§2). -/
def cost [LinearOrder α] (x : α) (t : BinaryTree α) : ℕ :=
  max 1 (rotations x t)

/-- **Subtree at the end of the search path.** `focus x t` is the subtree of `t` rooted at the
last node visited by the binary-search descent for `x`: the node containing `x` if `x` is
present, and otherwise the node whose missing child the search would follow. This is the node
that splaying moves to the root, and its subtree size is the `s(x)` of the Sleator–Tarjan access
lemma. -/
def focus [LinearOrder α] (x : α) : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node k l r =>
      if x = k then .node k l r
      else if x < k then
        match l with
        | .nil => .node k l r
        | .node _ _ _ => focus x l
      else
        match r with
        | .nil => .node k l r
        | .node _ _ _ => focus x r

section Arithmetic

private theorem lg_nonneg (n : ℕ) : 0 ≤ Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

private theorem lg_mono {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) :
    Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) :=
  Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm) (by exact_mod_cast h)

end Arithmetic

/-- **Weight of a binary tree.** The sum of the weights `w` of the keys stored in its nodes; for
`w = 1` it is the number of nodes. With positive weights, this is the size `s(x)` of Sleator and
Tarjan (*Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2). -/
def weight (w : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node k l r => weight w l + w k + weight w r

/-- **Weighted splay-tree potential.** The sum over the nodes of a binary tree of `log₂` of the
weight of the subtree rooted there: the potential of Sleator and Tarjan for item weights `w`
(*Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2). -/
noncomputable def potentialW (w : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node k l r => potentialW w l + potentialW w r + Real.logb 2 (weight w (.node k l r))

theorem weight_nonneg {w : α → ℝ} (hw : ∀ a, 0 < w a) : ∀ t : BinaryTree α, 0 ≤ weight w t
  | .nil => le_rfl
  | .node k l r => by
      have := weight_nonneg hw l
      have := weight_nonneg hw r
      have := hw k
      simp only [weight]
      linarith

theorem weight_node_pos {w : α → ℝ} (hw : ∀ a, 0 < w a) (k : α) (l r : BinaryTree α) :
    0 < weight w (.node k l r) := by
  have := weight_nonneg hw l
  have := weight_nonneg hw r
  have := hw k
  simp only [weight]
  linarith

theorem weight_eq_sum_inorder (w : α → ℝ) : ∀ t : BinaryTree α,
    weight w t = ((BinarySearchTree.inorder t).map w).sum
  | .nil => by simp [weight, BinarySearchTree.inorder, BinarySearchTree.inorderAux]
  | .node k l r => by
      rw [weight, weight_eq_sum_inorder w l, weight_eq_sum_inorder w r,
        BinarySearchTree.inorder_node]
      simp [List.sum_cons]
      ring

/-- **Splaying preserves the weight of a tree.** For every weight function `w`, the splayed tree
`splay x t` has the same weight as `t`, since splaying preserves the inorder sequence of keys. -/
theorem weight_splay [LinearOrder α] (w : α → ℝ) (x : α) (t : BinaryTree α) :
    weight w (splay x t) = weight w t := by
  rw [weight_eq_sum_inorder, weight_eq_sum_inorder, inorder_splay]

private theorem splay_eq_node_of_node_w [LinearOrder α] (w : α → ℝ) (x a : α)
    (b c : BinaryTree α) :
    ∃ d A B, splay x (.node a b c) = .node d A B ∧
      weight w A + w d + weight w B = weight w (.node a b c) := by
  cases hs : splay x (.node a b c) with
  | nil =>
      have h := numNodes_splay (x := x) (t := .node a b c)
      rw [hs] at h
      simp at h
  | node d A B =>
      refine ⟨d, A, B, rfl, ?_⟩
      have h := weight_splay w x (.node a b c)
      rw [hs] at h
      exact h

private theorem lgR_mono {a b : ℝ} (ha : 0 < a) (h : a ≤ b) :
    Real.logb 2 a ≤ Real.logb 2 b :=
  Real.logb_le_logb_of_le (by norm_num) ha h

private theorem lgR_add_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a + b ≤ c) :
    Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 c - 2 := by
  have hc : 0 < c := by linarith
  have hab : a * b ≤ c ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
  have hlog : Real.logb 2 (a * b) ≤ Real.logb 2 (c ^ 2 / 4) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hab
  have h4 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_mul ha.ne' hb.ne', Real.logb_div (by positivity) (by norm_num),
    Real.logb_pow, h4] at hlog
  push_cast at hlog
  linarith

private theorem zig_stepW {T K L : ℝ} (hK : 0 < K) (hKT : K ≤ T) (hL : 0 < L) (hLT : L ≤ T) :
    Real.logb 2 K - Real.logb 2 L ≤ 3 * (Real.logb 2 T - Real.logb 2 L) := by
  have h1 := lgR_mono hK hKT
  have h2 := lgR_mono hL hLT
  linarith

private theorem zigzig_stepW {T L M K N : ℝ} (hL : 0 < L) (hLM : L ≤ M) (hN : 0 < N)
    (hNT : N ≤ T) (hK : 0 < K) (hLK : L + K ≤ T) :
    2 + Real.logb 2 K + Real.logb 2 N - Real.logb 2 L - Real.logb 2 M ≤
      3 * (Real.logb 2 T - Real.logb 2 L) := by
  have h1 := lgR_mono hL hLM
  have h2 := lgR_mono hN hNT
  have h3 := lgR_add_le hL hK hLK
  linarith

private theorem zigzag_stepW {T L M K N : ℝ} (hL : 0 < L) (hLM : L ≤ M) (hLT : L ≤ T)
    (hN : 0 < N) (hK : 0 < K) (hNK : N + K ≤ T) :
    2 + Real.logb 2 N + Real.logb 2 K - Real.logb 2 L - Real.logb 2 M ≤
      3 * (Real.logb 2 T - Real.logb 2 L) := by
  have h1 := lgR_mono hL hLM
  have h2 := lgR_mono hL hLT
  have h3 := lgR_add_le hN hK hNK
  linarith

private theorem access_aux [LinearOrder α] {w : α → ℝ} (hw : ∀ a, 0 < w a) (x : α) (n : ℕ) :
    ∀ t : BinaryTree α, t.numNodes ≤ n →
      (cost x t : ℝ) + potentialW w (splay x t) - potentialW w t ≤
        3 * (Real.logb 2 (weight w t) - Real.logb 2 (weight w (focus x t))) + 1 := by
  induction n with
  | zero =>
      intro t ht
      cases t with
      | nil => rw [cost, rotations.eq_def]; simp [focus, potentialW, weight]
      | node _ _ _ => simp at ht
  | succ n ih =>
      intro t ht
      cases t with
      | nil => rw [cost, rotations.eq_def]; simp [focus, potentialW, weight]
      | node k l r =>
      by_cases hxk : x = k
      · -- the key is at the root: nothing happens
        subst hxk
        have hs : splay x (.node x l r) = .node x l r := by unfold splay; simp
        have hc : cost x (.node x l r) = 1 := by rw [cost, rotations.eq_def]; simp
        simp [hs, hc, focus]
      by_cases hlt : x < k
      · cases l with
        | nil =>
            have hs : splay x (.node k .nil r) = .node k .nil r := by
              unfold splay; simp [hxk, hlt]
            rw [cost, rotations.eq_def]; simp [focus, hs, hxk, hlt]
        | node lk ll lr =>
          by_cases hxl : x = lk
          · -- zig
            subst hxl
            have hs : splay x (.node k (.node x ll lr) r) = .node x ll (.node k lr r) := by
              unfold splay; simp [hxk, hlt]
            have hc : cost x (.node k (.node x ll lr) r) = 1 := by
              rw [cost, rotations.eq_def]; simp [hxk, hlt]
            have hf : focus x (.node k (.node x ll lr) r) = .node x ll lr := by
              simp [focus, hxk, hlt]
            rw [hs, hc, hf]
            have := weight_nonneg hw ll
            have := weight_nonneg hw lr
            have := weight_nonneg hw r
            have := hw x
            have := hw k
            have := zig_stepW (T := weight w (BinaryTree.node k (.node x ll lr) r))
              (K := weight w (BinaryTree.node k lr r)) (L := weight w (BinaryTree.node x ll lr))
              (by simp only [weight]; linarith)
              (by simp only [weight]; linarith)
              (by simp only [weight]; linarith)
              (by simp only [weight]; linarith)
            have hT : weight w (BinaryTree.node x ll (.node k lr r)) =
                weight w (BinaryTree.node k (.node x ll lr) r) := by simp only [weight]; linarith
            simp only [potentialW, hT]
            push_cast
            linarith
          by_cases hll : x < lk
          · cases ll with
            | nil =>
                -- fallback zig on `lk`
                have hs : splay x (.node k (.node lk .nil lr) r) =
                    .node lk .nil (.node k lr r) := by
                  unfold splay; simp [hxk, hlt, hxl, hll]
                have hc : cost x (.node k (.node lk .nil lr) r) = 1 := by
                  rw [cost, rotations.eq_def]; simp [hxk, hlt, hxl, hll]
                have hf : focus x (.node k (.node lk .nil lr) r) = .node lk .nil lr := by
                  simp [focus, hxk, hlt, hxl, hll]
                rw [hs, hc, hf]
                have := weight_nonneg hw lr
                have := weight_nonneg hw r
                have := hw lk
                have := hw k
                have := zig_stepW (T := weight w (BinaryTree.node k (.node lk .nil lr) r))
                  (K := weight w (BinaryTree.node k lr r))
                  (L := weight w (BinaryTree.node lk .nil lr))
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node lk .nil (.node k lr r)) =
                    weight w (BinaryTree.node k (.node lk .nil lr) r) := by
                  simp only [weight]; linarith
                simp only [potentialW, hT]
                push_cast
                linarith
            | node a b c =>
                -- zig-zig
                obtain ⟨d, A, B, hsp, hAB⟩ := splay_eq_node_of_node_w w x a b c
                have hs : splay x (.node k (.node lk (.node a b c) lr) r) =
                    .node d A (.node lk B (.node k lr r)) := by
                  unfold splay; simp [hxk, hlt, hxl, hll, hsp]
                have hrot : rotations x (.node k (.node lk (.node a b c) lr) r) =
                    rotations x (.node a b c) + 2 := by
                  rw [rotations.eq_def]; simp [hxk, hlt, hxl, hll]
                have hc : cost x (.node k (.node lk (.node a b c) lr) r) =
                    rotations x (.node a b c) + 2 := by
                  rw [cost, hrot]; omega
                have hf : focus x (.node k (.node lk (.node a b c) lr) r) =
                    focus x (.node a b c) := by
                  simp [focus, hxk, hlt, hxl, hll]
                have hsize : (BinaryTree.node a b c).numNodes ≤ n := by
                  simp only [BinaryTree.numNodes] at ht ⊢; omega
                have hih := ih (.node a b c) hsize
                have hcle : (rotations x (.node a b c) : ℝ) ≤ cost x (.node a b c) := by
                  exact_mod_cast le_max_right _ _
                rw [hsp] at hih
                rw [hs, hc, hf]
                set ll : BinaryTree α := .node a b c with hlldef
                have hll1 : 0 < weight w ll := weight_node_pos hw a b c
                have := weight_nonneg hw A
                have := weight_nonneg hw B
                have := weight_nonneg hw ll
                have := weight_nonneg hw lr
                have := weight_nonneg hw r
                have := hw d
                have := hw lk
                have := hw k
                have := zigzig_stepW (T := weight w (BinaryTree.node k (.node lk ll lr) r))
                  (L := weight w ll) (M := weight w (BinaryTree.node lk ll lr))
                  (K := weight w (BinaryTree.node k lr r))
                  (N := weight w (BinaryTree.node lk B (.node k lr r)))
                  hll1 (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node d A (.node lk B (.node k lr r))) =
                    weight w (BinaryTree.node k (.node lk ll lr) r) := by
                  simp only [weight]; linarith
                have hD : weight w (BinaryTree.node d A B) = weight w ll := by
                  simp only [weight]; linarith
                simp only [potentialW, hT] at hih ⊢
                rw [hD] at hih
                push_cast at hih ⊢
                linarith
          · cases lr with
            | nil =>
                have hs : splay x (.node k (.node lk ll .nil) r) =
                    .node lk ll (.node k .nil r) := by
                  unfold splay; simp [hxk, hlt, hxl, hll]
                have hc : cost x (.node k (.node lk ll .nil) r) = 1 := by
                  rw [cost, rotations.eq_def]; simp [hxk, hlt, hxl, hll]
                have hf : focus x (.node k (.node lk ll .nil) r) = .node lk ll .nil := by
                  simp [focus, hxk, hlt, hxl, hll]
                rw [hs, hc, hf]
                have := weight_nonneg hw ll
                have := weight_nonneg hw r
                have := hw lk
                have := hw k
                have := zig_stepW (T := weight w (BinaryTree.node k (.node lk ll .nil) r))
                  (K := weight w (BinaryTree.node k .nil r))
                  (L := weight w (BinaryTree.node lk ll .nil))
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node lk ll (.node k .nil r)) =
                    weight w (BinaryTree.node k (.node lk ll .nil) r) := by
                  simp only [weight]; linarith
                simp only [potentialW, hT]
                push_cast
                linarith
            | node a b c =>
                -- zig-zag
                obtain ⟨d, A, B, hsp, hAB⟩ := splay_eq_node_of_node_w w x a b c
                have hs : splay x (.node k (.node lk ll (.node a b c)) r) =
                    .node d (.node lk ll A) (.node k B r) := by
                  unfold splay; simp [hxk, hlt, hxl, hll, hsp]
                have hrot : rotations x (.node k (.node lk ll (.node a b c)) r) =
                    rotations x (.node a b c) + 2 := by
                  rw [rotations.eq_def]; simp [hxk, hlt, hxl, hll]
                have hc : cost x (.node k (.node lk ll (.node a b c)) r) =
                    rotations x (.node a b c) + 2 := by
                  rw [cost, hrot]; omega
                have hf : focus x (.node k (.node lk ll (.node a b c)) r) =
                    focus x (.node a b c) := by
                  simp [focus, hxk, hlt, hxl, hll]
                have hsize : (BinaryTree.node a b c).numNodes ≤ n := by
                  simp only [BinaryTree.numNodes] at ht ⊢; omega
                have hih := ih (.node a b c) hsize
                have hcle : (rotations x (.node a b c) : ℝ) ≤ cost x (.node a b c) := by
                  exact_mod_cast le_max_right _ _
                rw [hsp] at hih
                rw [hs, hc, hf]
                set lr : BinaryTree α := .node a b c with hlrdef
                have hlr1 : 0 < weight w lr := weight_node_pos hw a b c
                have := weight_nonneg hw ll
                have := weight_nonneg hw A
                have := weight_nonneg hw B
                have := weight_nonneg hw lr
                have := weight_nonneg hw r
                have := hw d
                have := hw lk
                have := hw k
                have := zigzag_stepW (T := weight w (BinaryTree.node k (.node lk ll lr) r))
                  (L := weight w lr) (M := weight w (BinaryTree.node lk ll lr))
                  (N := weight w (BinaryTree.node lk ll A))
                  (K := weight w (BinaryTree.node k B r))
                  hlr1 (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node d (.node lk ll A) (.node k B r)) =
                    weight w (BinaryTree.node k (.node lk ll lr) r) := by
                  simp only [weight]; linarith
                have hD : weight w (BinaryTree.node d A B) = weight w lr := by
                  simp only [weight]; linarith
                simp only [potentialW, hT] at hih ⊢
                rw [hD] at hih
                push_cast at hih ⊢
                linarith
      · cases r with
        | nil =>
            have hs : splay x (.node k l .nil) = .node k l .nil := by
              unfold splay; simp [hxk, hlt]
            rw [cost, rotations.eq_def]; simp [focus, hs, hxk, hlt]
        | node rk rl rr =>
          by_cases hxr : x = rk
          · -- zig
            subst hxr
            have hs : splay x (.node k l (.node x rl rr)) = .node x (.node k l rl) rr := by
              unfold splay; simp [hxk, hlt]
            have hc : cost x (.node k l (.node x rl rr)) = 1 := by
              rw [cost, rotations.eq_def]; simp [hxk, hlt]
            have hf : focus x (.node k l (.node x rl rr)) = .node x rl rr := by
              simp [focus, hxk, hlt]
            rw [hs, hc, hf]
            have := weight_nonneg hw l
            have := weight_nonneg hw rl
            have := weight_nonneg hw rr
            have := hw x
            have := hw k
            have := zig_stepW (T := weight w (BinaryTree.node k l (.node x rl rr)))
              (K := weight w (BinaryTree.node k l rl)) (L := weight w (BinaryTree.node x rl rr))
              (by simp only [weight]; linarith)
              (by simp only [weight]; linarith)
              (by simp only [weight]; linarith)
              (by simp only [weight]; linarith)
            have hT : weight w (BinaryTree.node x (.node k l rl) rr) =
                weight w (BinaryTree.node k l (.node x rl rr)) := by simp only [weight]; linarith
            simp only [potentialW, hT]
            push_cast
            linarith
          by_cases hrr : rk < x
          · have hnot : ¬ x < rk := not_lt.mpr hrr.le
            cases rr with
            | nil =>
                have hs : splay x (.node k l (.node rk rl .nil)) =
                    .node rk (.node k l rl) .nil := by
                  unfold splay; simp [hxk, hlt, hxr, hrr]
                have hc : cost x (.node k l (.node rk rl .nil)) = 1 := by
                  rw [cost, rotations.eq_def]; simp [hxk, hlt, hxr, hrr]
                have hf : focus x (.node k l (.node rk rl .nil)) = .node rk rl .nil := by
                  simp [focus, hxk, hlt, hxr, hnot]
                rw [hs, hc, hf]
                have := weight_nonneg hw l
                have := weight_nonneg hw rl
                have := hw rk
                have := hw k
                have := zig_stepW (T := weight w (BinaryTree.node k l (.node rk rl .nil)))
                  (K := weight w (BinaryTree.node k l rl))
                  (L := weight w (BinaryTree.node rk rl .nil))
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node rk (.node k l rl) .nil) =
                    weight w (BinaryTree.node k l (.node rk rl .nil)) := by
                  simp only [weight]; linarith
                simp only [potentialW, hT]
                push_cast
                linarith
            | node a b c =>
                -- zig-zig
                obtain ⟨d, A, B, hsp, hAB⟩ := splay_eq_node_of_node_w w x a b c
                have hs : splay x (.node k l (.node rk rl (.node a b c))) =
                    .node d (.node rk (.node k l rl) A) B := by
                  unfold splay; simp [hxk, hlt, hxr, hrr, hsp]
                have hrot : rotations x (.node k l (.node rk rl (.node a b c))) =
                    rotations x (.node a b c) + 2 := by
                  rw [rotations.eq_def]; simp [hxk, hlt, hxr, hrr]
                have hc : cost x (.node k l (.node rk rl (.node a b c))) =
                    rotations x (.node a b c) + 2 := by
                  rw [cost, hrot]; omega
                have hf : focus x (.node k l (.node rk rl (.node a b c))) =
                    focus x (.node a b c) := by
                  simp [focus, hxk, hlt, hxr, hnot]
                have hsize : (BinaryTree.node a b c).numNodes ≤ n := by
                  simp only [BinaryTree.numNodes] at ht ⊢; omega
                have hih := ih (.node a b c) hsize
                have hcle : (rotations x (.node a b c) : ℝ) ≤ cost x (.node a b c) := by
                  exact_mod_cast le_max_right _ _
                rw [hsp] at hih
                rw [hs, hc, hf]
                set rr : BinaryTree α := .node a b c with hrrdef
                have hrr1 : 0 < weight w rr := weight_node_pos hw a b c
                have := weight_nonneg hw l
                have := weight_nonneg hw rl
                have := weight_nonneg hw A
                have := weight_nonneg hw B
                have := weight_nonneg hw rr
                have := hw d
                have := hw rk
                have := hw k
                have := zigzig_stepW (T := weight w (BinaryTree.node k l (.node rk rl rr)))
                  (L := weight w rr) (M := weight w (BinaryTree.node rk rl rr))
                  (K := weight w (BinaryTree.node k l rl))
                  (N := weight w (BinaryTree.node rk (.node k l rl) A))
                  hrr1 (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node d (.node rk (.node k l rl) A) B) =
                    weight w (BinaryTree.node k l (.node rk rl rr)) := by
                  simp only [weight]; linarith
                have hD : weight w (BinaryTree.node d A B) = weight w rr := by
                  simp only [weight]; linarith
                simp only [potentialW, hT] at hih ⊢
                rw [hD] at hih
                push_cast at hih ⊢
                linarith
          · have hlt' : x < rk := lt_of_le_of_ne (not_lt.mp hrr) hxr
            cases rl with
            | nil =>
                have hs : splay x (.node k l (.node rk .nil rr)) =
                    .node rk (.node k l .nil) rr := by
                  unfold splay; simp [hxk, hlt, hxr, hrr]
                have hc : cost x (.node k l (.node rk .nil rr)) = 1 := by
                  rw [cost, rotations.eq_def]; simp [hxk, hlt, hxr, hrr]
                have hf : focus x (.node k l (.node rk .nil rr)) = .node rk .nil rr := by
                  simp [focus, hxk, hlt, hxr, hlt']
                rw [hs, hc, hf]
                have := weight_nonneg hw l
                have := weight_nonneg hw rr
                have := hw rk
                have := hw k
                have := zig_stepW (T := weight w (BinaryTree.node k l (.node rk .nil rr)))
                  (K := weight w (BinaryTree.node k l .nil))
                  (L := weight w (BinaryTree.node rk .nil rr))
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node rk (.node k l .nil) rr) =
                    weight w (BinaryTree.node k l (.node rk .nil rr)) := by
                  simp only [weight]; linarith
                simp only [potentialW, hT]
                push_cast
                linarith
            | node a b c =>
                -- zig-zag
                obtain ⟨d, A, B, hsp, hAB⟩ := splay_eq_node_of_node_w w x a b c
                have hs : splay x (.node k l (.node rk (.node a b c) rr)) =
                    .node d (.node k l A) (.node rk B rr) := by
                  unfold splay; simp [hxk, hlt, hxr, hrr, hsp]
                have hrot : rotations x (.node k l (.node rk (.node a b c) rr)) =
                    rotations x (.node a b c) + 2 := by
                  rw [rotations.eq_def]; simp [hxk, hlt, hxr, hrr]
                have hc : cost x (.node k l (.node rk (.node a b c) rr)) =
                    rotations x (.node a b c) + 2 := by
                  rw [cost, hrot]; omega
                have hf : focus x (.node k l (.node rk (.node a b c) rr)) =
                    focus x (.node a b c) := by
                  simp [focus, hxk, hlt, hxr, hlt']
                have hsize : (BinaryTree.node a b c).numNodes ≤ n := by
                  simp only [BinaryTree.numNodes] at ht ⊢; omega
                have hih := ih (.node a b c) hsize
                have hcle : (rotations x (.node a b c) : ℝ) ≤ cost x (.node a b c) := by
                  exact_mod_cast le_max_right _ _
                rw [hsp] at hih
                rw [hs, hc, hf]
                set rl : BinaryTree α := .node a b c with hrldef
                have hrl1 : 0 < weight w rl := weight_node_pos hw a b c
                have := weight_nonneg hw l
                have := weight_nonneg hw A
                have := weight_nonneg hw B
                have := weight_nonneg hw rl
                have := weight_nonneg hw rr
                have := hw d
                have := hw rk
                have := hw k
                have := zigzag_stepW (T := weight w (BinaryTree.node k l (.node rk rl rr)))
                  (L := weight w rl) (M := weight w (BinaryTree.node rk rl rr))
                  (N := weight w (BinaryTree.node k l A))
                  (K := weight w (BinaryTree.node rk B rr))
                  hrl1 (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                  (by simp only [weight]; linarith)
                have hT : weight w (BinaryTree.node d (.node k l A) (.node rk B rr)) =
                    weight w (BinaryTree.node k l (.node rk rl rr)) := by
                  simp only [weight]; linarith
                have hD : weight w (BinaryTree.node d A B) = weight w rl := by
                  simp only [weight]; linarith
                simp only [potentialW, hT] at hih ⊢
                rw [hD] at hih
                push_cast at hih ⊢
                linarith

/-- **Access lemma for splay trees.** For every assignment of positive weights `w` to the keys,
every binary tree `t` and every key `x`, the amortized cost of splaying `t` at `x`, namely its
cost (rotations, or one if none) plus the change in the weighted potential, is at most
`3 (log₂ W(t) - log₂ W(focus x t)) + 1`, where `W` is the total weight of a subtree and
`focus x t` is the subtree rooted at the node that splaying brings to the root (Sleator and
Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985), Lemma 1 (Access Lemma)).
No search-tree ordering is needed. -/
theorem access_lemma_weighted [LinearOrder α] {w : α → ℝ} (hw : ∀ a, 0 < w a) (x : α)
    (t : BinaryTree α) :
    (cost x t : ℝ) + potentialW w (splay x t) - potentialW w t ≤
      3 * (Real.logb 2 (weight w t) - Real.logb 2 (weight w (focus x t))) + 1 :=
  access_aux hw x t.numNodes t le_rfl

/-- **Unit weights give the number of nodes.** With every weight equal to one, the weight of a
binary tree is its number of nodes. -/
theorem weight_one : ∀ t : BinaryTree α, weight (fun _ => (1 : ℝ)) t = t.numNodes
  | .nil => by simp [weight]
  | .node k l r => by
      rw [weight, weight_one l, weight_one r]
      push_cast [BinaryTree.numNodes]
      ring

/-- **Unit-weight potential is the splay-tree potential.** With every weight equal to one, the
weighted potential `potentialW` of a binary tree equals its unit-weight potential `potential`. -/
theorem potential_eq_potentialW_one : ∀ t : BinaryTree α,
    potential t = potentialW (fun _ => (1 : ℝ)) t
  | .nil => rfl
  | .node k l r => by
      rw [potential, potentialW, potential_eq_potentialW_one l, potential_eq_potentialW_one r,
        weight_one]

/-- **Access lemma for splay trees (unit weights).** For every binary tree `t` and key `x`, the
amortized cost of splaying `t` at `x`, namely its cost (rotations, or one if none) plus the
change in the sum-of-logs potential, is at most `3 (log₂ |t| - log₂ |focus x t|) + 1`, where
`|·|` is the number of nodes and `focus x t` is the subtree rooted at the node that splaying
brings to the root (Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3)
(1985), Lemma 1 (Access Lemma), with all weights equal to one). No search-tree ordering is
needed. -/
theorem access_lemma [LinearOrder α] (x : α) (t : BinaryTree α) :
    (cost x t : ℝ) + potential (splay x t) - potential t ≤
      3 * (Real.logb 2 (t.numNodes : ℝ) - Real.logb 2 ((focus x t).numNodes : ℝ)) + 1 := by
  have h := access_lemma_weighted (w := fun _ : α => (1 : ℝ)) (fun _ => one_pos) x t
  rwa [← potential_eq_potentialW_one, ← potential_eq_potentialW_one, weight_one,
    weight_one] at h

/-- **Amortized cost of a splay is at most `3 log₂ n + 1`.** On a tree with `n` nodes, the
cost of `splay x t` plus the change in potential is at most `3 log₂ n + 1` (Sleator and
Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985), Lemma 1 with unit weights,
as used in the proof of Theorem 1). -/
theorem amortized_cost_le [LinearOrder α] (x : α) (t : BinaryTree α) :
    (cost x t : ℝ) + potential (splay x t) - potential t ≤
      3 * Real.logb 2 (t.numNodes : ℝ) + 1 := by
  have h := access_lemma x t
  have := lg_nonneg (focus x t).numNodes
  linarith

/-- **The splay-tree potential is nonnegative.** Every term of the potential is `log₂` of a
subtree size, which is at least one. -/
theorem potential_nonneg : ∀ t : BinaryTree α, 0 ≤ potential t
  | .nil => le_rfl
  | .node k l r => by
      have := potential_nonneg l
      have := potential_nonneg r
      have := lg_nonneg (BinaryTree.node k l r).numNodes
      simp only [potential]
      linarith

/-- **Upper bound on the splay-tree potential.** A tree with `n` nodes has potential at most
`n log₂ n`, since each of its `n` subtrees has at most `n` nodes (Sleator and Tarjan,
*Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2, the bound on the net potential
drop before Theorem 1, with unit weights). -/
theorem potential_le : ∀ t : BinaryTree α,
    potential t ≤ (t.numNodes : ℝ) * Real.logb 2 (t.numNodes : ℝ)
  | .nil => by simp [potential]
  | .node k l r => by
      have hl := potential_le l
      have hr := potential_le r
      have hT : 1 ≤ (BinaryTree.node k l r).numNodes := by simp
      have hlT : l.numNodes * Real.logb 2 (l.numNodes : ℝ) ≤
          l.numNodes * Real.logb 2 ((BinaryTree.node k l r).numNodes : ℝ) := by
        rcases Nat.eq_zero_or_pos l.numNodes with h0 | h0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (lg_mono h0 (by simp; omega)) (by positivity)
      have hrT : r.numNodes * Real.logb 2 (r.numNodes : ℝ) ≤
          r.numNodes * Real.logb 2 ((BinaryTree.node k l r).numNodes : ℝ) := by
        rcases Nat.eq_zero_or_pos r.numNodes with h0 | h0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (lg_mono h0 (by simp; omega)) (by positivity)
      have hsum : ((BinaryTree.node k l r).numNodes : ℝ) =
          (l.numNodes : ℝ) + r.numNodes + 1 := by simp
      simp only [potential]
      rw [hsum] at ⊢
      rw [hsum] at hlT hrT
      nlinarith

/-- **Trees of a run of splays.** `splayRun xs t i` is the tree obtained from `t` by splaying
successively at `xs 0, xs 1, …, xs (i - 1)`. -/
def splayRun [LinearOrder α] (xs : ℕ → α) (t : BinaryTree α) : ℕ → BinaryTree α
  | 0 => t
  | i + 1 => splay (xs i) (splayRun xs t i)

/-- **Splaying preserves the number of nodes along a run.** Every tree `splayRun xs t i` has as
many nodes as `t`. -/
theorem numNodes_splayRun [LinearOrder α] (xs : ℕ → α) (t : BinaryTree α) :
    ∀ i, (splayRun xs t i).numNodes = t.numNodes
  | 0 => rfl
  | i + 1 => by rw [splayRun, numNodes_splay, numNodes_splayRun xs t i]

/-- **Balance theorem for splay trees.** Starting from any binary tree with `n` nodes, `m`
successive splays cost in total at most `m (3 log₂ n + 1) + n log₂ n`, where the cost of a
splay is its number of rotations, or one if it performs none. This is the explicit form of
Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985), Theorem 1
(Balance Theorem), "the total access time is `O((m + n) log n + m)`", obtained, as in their
proof, from the access lemma and the potential method. -/
theorem balance_theorem [LinearOrder α] (xs : ℕ → α) (t : BinaryTree α) (m : ℕ) :
    (∑ i ∈ Finset.range m, (cost (xs i) (splayRun xs t i) : ℝ)) ≤
      m * (3 * Real.logb 2 (t.numNodes : ℝ) + 1) +
        t.numNodes * Real.logb 2 (t.numNodes : ℝ) := by
  have key := PotentialMethod.sum_cost_le_of_amortizedCost_le potential (splayRun xs t)
    (fun i => (cost (xs i) (splayRun xs t i) : ℝ))
    (fun _ => 3 * Real.logb 2 (t.numNodes : ℝ) + 1) m (by
      intro i _
      have h := amortized_cost_le (xs i) (splayRun xs t i)
      rw [numNodes_splayRun] at h
      simpa [PotentialMethod.amortizedCost, splayRun] using h)
  have h0 : potential (splayRun xs t 0) ≤ t.numNodes * Real.logb 2 (t.numNodes : ℝ) :=
    potential_le t
  have hm := potential_nonneg (splayRun xs t m)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  linarith

/-- **Number of rotations performed by `splayMax`.** `rotationsMax t` counts the single
rotations performed by `SplayTree.splayMax t`: one for a zig step and two for a
zig-zig step, mirroring the recursion of `splayMax` (Sleator and Tarjan, §2, for the
maximum). No ordering is needed. -/
def rotationsMax : BinaryTree α → ℕ
  | .nil => 0
  | .node _ _ .nil => 0
  | .node _ _ (.node _ _ rr) =>
      match splayMax rr with
      | .nil => 1
      | .node _ _ _ => rotationsMax rr + 2

/-- **Cost of `splayMax`.** The number of rotations performed by `SplayTree.splayMax t`,
or one if there are none, following the cost model of `cost` (Sleator and Tarjan, §2). -/
def costMax (t : BinaryTree α) : ℕ :=
  max 1 (rotationsMax t)

/-- **Cost of `delete`.** The cost of `SplayTree.delete x t`: the cost of the splay,
plus the cost of `splayMax` on the left subtree when `x` is found (Nipkow, FDSA §21.1). -/
def costDelete [LinearOrder α] (x : α) (t : BinaryTree α) : ℕ :=
  match splay x t with
  | .nil => 1
  | .node a l _r => if x = a then cost x t + costMax l else cost x t

/-- **Cost of the book's insert.** The cost of `SplayTree.nipkowInsert x t`: the cost
of the splay; the rebuilding of the tree around the new root is free, as in Nipkow's
time function `Tinsert = Tsplay` (FDSA Appendix B.9). It charges the book's
splay-then-rebuild: `SplayTree.insert x t` is the same tree (`insert_eq_nipkowInsert`),
but the `split` that `SplayTree.insert` performs instead of the rebuild is not charged. -/
def costInsert [LinearOrder α] (x : α) (t : BinaryTree α) : ℕ :=
  cost x t

private theorem rotationsMax_node_node_of_nil {k rk : α} {l rl rr : BinaryTree α}
    (h : splayMax rr = .nil) :
    rotationsMax (.node k l (.node rk rl rr)) = 1 := by
  unfold rotationsMax
  simp [h]

private theorem rotationsMax_node_node_of_node {k rk c : α} {l rl rr C D : BinaryTree α}
    (h : splayMax rr = .node c C D) :
    rotationsMax (.node k l (.node rk rl rr)) = rotationsMax rr + 2 := by
  have heq : rotationsMax (.node k l (.node rk rl rr)) =
      match splayMax rr with
      | .nil => 1
      | .node _ _ _ => rotationsMax rr + 2 := rfl
  rw [heq, h]

private theorem costDelete_eq_of_nil [LinearOrder α] {x : α} {t : BinaryTree α}
    (hsp : splay x t = .nil) : costDelete x t = 1 := by
  unfold costDelete
  rw [hsp]

private theorem costDelete_eq_of_ne [LinearOrder α] {x a : α} {t l r : BinaryTree α}
    (hsp : splay x t = .node a l r) (hxa : x ≠ a) : costDelete x t = cost x t := by
  unfold costDelete
  rw [hsp]
  simp [hxa]

private theorem costDelete_eq_of_eq [LinearOrder α] {x a : α} {t l r : BinaryTree α}
    (hsp : splay x t = .node a l r) (hxa : x = a) :
    costDelete x t = cost x t + costMax l := by
  unfold costDelete
  rw [hsp]
  simp [hxa]

/-- **Logarithm monotonicity, including zero.** `log₂ m ≤ log₂ n` for `m ≤ n`, with
`log₂ 0 = 0`. -/
private theorem logb_mono_zero {m n : ℕ} (h : m ≤ n) :
    Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.logb_zero]
    exact lg_nonneg n
  · exact lg_mono h0 h

/-- **`log₂ (n + 1) ≤ log₂ n + 1` for `n ≥ 1`.** Since `n + 1 ≤ 2n`. -/
private theorem logb_succ_le {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (((n + 1 : ℕ) : ℝ)) ≤ Real.logb 2 (n : ℝ) + 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    push_cast
    linarith
  have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast Nat.succ_pos n) hle
  have h2 : Real.logb 2 (2 * (n : ℝ)) = Real.logb 2 (n : ℝ) + 1 := by
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnpos),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    ring
  linarith

/-- **Potential of a splay with known root.** If `splay x t` has root `a` with
subtrees `l` and `r`, its potential is `potential l + potential r + log₂ |t|`. -/
private theorem potential_splay_eq_of_eq [LinearOrder α] {x a : α} {t l r : BinaryTree α}
    (hs : splay x t = .node a l r) :
    potential (splay x t) = potential l + potential r + Real.logb 2 (t.numNodes : ℝ) := by
  have hnum : (BinaryTree.node a l r).numNodes = t.numNodes := by
    rw [← hs]
    exact numNodes_splay
  rw [hs]
  simp only [potential, hnum]

/-- **Potential of a `splayMax` with known root.** If `splayMax t` has root `m` with
subtrees `l'` and `D`, its potential is `potential l' + potential D + log₂ |t|`. -/
private theorem potential_splayMax_eq_of_eq_node {m : α} {t l' D : BinaryTree α}
    (hmax : splayMax t = .node m l' D) :
    potential (splayMax t) = potential l' + potential D + Real.logb 2 (t.numNodes : ℝ) := by
  have hnum : (BinaryTree.node m l' D).numNodes = t.numNodes := by
    rw [← hmax]
    exact numNodes_splayMax
  rw [hmax]
  simp only [potential, hnum]

/-- **Potential of a deletion with known shape.** If `splay x t` has root `x` with
subtrees `l` and `r`, and `splayMax l` has root `m` with left subtree `l'`, the
deleted tree has potential `potential l' + potential r + log₂ (|t| - 1)`. -/
private theorem potential_delete_eq_of_eq_node [LinearOrder α] {x a m : α}
    {t l r l' D : BinaryTree α} (hsp : splay x t = .node a l r) (hxa : x = a)
    (hmax : splayMax l = .node m l' D) :
    potential (delete x t) =
      potential l' + potential r + Real.logb 2 (((t.numNodes - 1 : ℕ) : ℝ)) := by
  obtain ⟨-, hin⟩ := splayMax_eq_node hmax
  have hlen : l'.numNodes + 1 = l.numNodes := by
    have h1 := congrArg List.length hin
    rw [List.length_append, List.length_singleton] at h1
    rw [← BinarySearchTree.numNodes_eq_length_inorder,
      ← BinarySearchTree.numNodes_eq_length_inorder] at h1
    exact h1
  have ht : t.numNodes = l.numNodes + r.numNodes + 1 := by
    have h1 : (BinaryTree.node a l r).numNodes = t.numNodes := by
      rw [← hsp]
      exact numNodes_splay
    simp only [BinaryTree.numNodes] at h1
    omega
  have hnum : (BinaryTree.node m l' r).numNodes = t.numNodes - 1 := by
    simp only [BinaryTree.numNodes]
    omega
  rw [delete_eq_of_eq_node hsp hxa hmax]
  simp only [potential, hnum]

/-- **Splaying for the maximum costs as many rotations as splaying for that key.**
On a search tree, `splayMax t` performs exactly the rotations that `splay a t`
performs when `a` is at least every key of `t`: the search for `a` always turns
right, so the two recursions take the same zig-zig steps. -/
private theorem rotationsMax_eq_rotations_aux [LinearOrder α] (n : Nat) (t : BinaryTree α)
    (h : t.numNodes ≤ n) (hOrd : BinarySearchTree.Ordered t) {a : α}
    (ha : ∀ y ∈ t, y ≤ a) :
    rotationsMax t = rotations a t := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil => rfl
      | node k l r => simp only [BinaryTree.numNodes] at h; omega
  | succ n ih =>
      cases t with
      | nil => rfl
      | node k l r =>
          cases r with
          | nil =>
              have hk : k ≤ a := ha k (Or.inr (Or.inl rfl))
              have hrot : rotations a (.node k l .nil) = 0 := by
                rw [rotations.eq_def]
                by_cases hak : a = k
                · simp [hak]
                · have hka : k < a := lt_of_le_of_ne hk (fun hh => hak hh.symm)
                  simp [hak, not_lt.mpr (le_of_lt hka)]
              calc rotationsMax (.node k l .nil) = 0 := rfl
                _ = rotations a (.node k l .nil) := hrot.symm
          | node rk rl rr =>
              obtain ⟨hOrdL, hOrdR, hAllL, hAllR⟩ := hOrd
              obtain ⟨-, hkrk, -⟩ := hAllR
              have hka : k < a :=
                lt_of_lt_of_le hkrk (ha rk (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
              have hrka : rk ≤ a := ha rk (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              rcases lt_trichotomy a rk with hlt | heq | hgt
              · exact absurd (lt_of_lt_of_le hlt hrka) (lt_irrefl a)
              · have hrr : rr = .nil := by
                  cases rr with
                  | nil => rfl
                  | node s b c =>
                      exfalso
                      have hsle : s ≤ a :=
                        ha s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                      obtain ⟨-, -, -, hAllR2⟩ := hOrdR
                      obtain ⟨-, hrks, -⟩ := hAllR2
                      rw [heq] at hsle
                      exact absurd (lt_of_lt_of_le hrks hsle) (lt_irrefl rk)
                subst hrr
                have hrot : rotations a (.node k l (.node rk rl .nil)) = 1 := by
                  rw [rotations.eq_def]
                  simp [ne_of_gt hkrk, not_lt.mpr (le_of_lt hkrk), heq]
                calc rotationsMax (.node k l (.node rk rl .nil)) = 1 :=
                      rotationsMax_node_node_of_nil rfl
                  _ = rotations a (.node k l (.node rk rl .nil)) := hrot.symm
              · cases rr with
                | nil =>
                    have hrot : rotations a (.node k l (.node rk rl .nil)) = 1 := by
                      rw [rotations.eq_def]
                      simp [ne_of_gt hka, not_lt.mpr (le_of_lt hka), ne_of_gt hgt, hgt]
                    calc rotationsMax (.node k l (.node rk rl .nil)) = 1 :=
                          rotationsMax_node_node_of_nil rfl
                      _ = rotations a (.node k l (.node rk rl .nil)) := hrot.symm
                | node s b c =>
                    cases hsp : splayMax (.node s b c) with
                    | nil => exact absurd hsp (splayMax_ne_nil (by simp))
                    | node cc C D =>
                        have hrot : rotations a (.node k l (.node rk rl (.node s b c))) =
                            rotations a (.node s b c) + 2 := by
                          rw [rotations.eq_def]
                          simp [ne_of_gt hka, not_lt.mpr (le_of_lt hka), ne_of_gt hgt, hgt]
                        have hih : rotationsMax (.node s b c) = rotations a (.node s b c) := by
                          apply ih
                          · simp only [BinaryTree.numNodes] at h ⊢
                            omega
                          · obtain ⟨-, hOrdRR, -, -⟩ := hOrdR
                            exact hOrdRR
                          · intro y hy
                            exact ha y (Or.inr (Or.inr (Or.inr (Or.inr hy))))
                        calc rotationsMax (.node k l (.node rk rl (.node s b c)))
                            = rotationsMax (.node s b c) + 2 :=
                              rotationsMax_node_node_of_node hsp
                          _ = rotations a (.node s b c) + 2 := by rw [hih]
                          _ = rotations a (.node k l (.node rk rl (.node s b c))) :=
                              hrot.symm

/-- **Splaying for the maximum costs as many rotations as splaying for that key.** -/
public theorem rotationsMax_eq_rotations [LinearOrder α] {t : BinaryTree α}
    (hOrd : BinarySearchTree.Ordered t) {a : α} (ha : ∀ y ∈ t, y ≤ a) :
    rotationsMax t = rotations a t :=
  rotationsMax_eq_rotations_aux t.numNodes t (by omega) hOrd ha

/-- **Amortized cost of `splayMax` is at most `3 log₂ n + 1`.** Splaying the maximum
to the root costs, in the amortized sense, at most `3 log₂ n + 1` on an `n`-node
search tree in this file's rotation-based cost model (rotations, or 1 if none;
`potential` sums `log₂` of subtree sizes): `splayMax t` is `splay a t` for the
maximum key `a`, and the access lemma applies. This is the repo's analogue of the
FDSA/AFP `A_splay_max` bound, not FDSA's statement: AFP's `A_splay_max_ub3`
states `3 * φ t + 1`, with `φ t = log₂ (size1 t)`. -/
public theorem amortized_splayMax_le [LinearOrder α] (t : BinaryTree α)
    (hOrd : BinarySearchTree.Ordered t) :
    (costMax t : ℝ) + potential (splayMax t) - potential t ≤
      3 * Real.logb 2 (t.numNodes : ℝ) + 1 := by
  cases t with
  | nil => simp [costMax, rotationsMax, splayMax_nil, potential, Real.logb_zero]
  | node k l r =>
      obtain ⟨a, ha, hEq⟩ := exists_max_splay hOrd (by simp)
      have hcost : costMax (.node k l r) = cost a (.node k l r) := by
        simp only [costMax, cost, rotationsMax_eq_rotations hOrd ha]
      rw [hEq, hcost]
      have h := access_lemma a (.node k l r)
      have hlog := lg_nonneg ((focus a (.node k l r)).numNodes)
      linarith

/-- **Amortized cost of `delete` is at most `5 log₂ n + 2`.** Deleting from an `n`-node
search tree costs, in the amortized sense, at most `5 log₂ n + 2` in this file's
rotation-based cost model (rotations, or 1 if none; `potential` sums `log₂` of
subtree sizes). In the main case (after the splay the key is at the root and its
left subtree `l` is nonempty), the splay contributes at most `3 log₂ n + 1` (access
lemma) and the `splayMax` on `l` at most `3 log₂ |l| + 1`; replacing the root by the
maximum of `l` then changes the potential by `log₂ (n - 1) - log₂ n - log₂ |l|`,
which is at most `-log₂ |l|`. The total is therefore at most
`3 log₂ n + 2 log₂ |l| + 2 ≤ 5 log₂ n + 2`. This is the repo's analogue of the
FDSA/AFP `A_delete` bound, not FDSA's statement: AFP's `amor_delete` proves
`6 * log 2 (size1 t) + 2` in AFP's own time-function and potential model. -/
public theorem amortized_delete_le [LinearOrder α] (x : α) (t : BinaryTree α)
    (hOrd : BinarySearchTree.Ordered t) :
    (costDelete x t : ℝ) + potential (delete x t) - potential t ≤
      5 * Real.logb 2 (t.numNodes : ℝ) + 2 := by
  cases hs : splay x t with
  | nil =>
      have ht : t = .nil := splay_eq_nil.mp hs
      subst ht
      have hc : costDelete x (.nil : BinaryTree α) = 1 := costDelete_eq_of_nil hs
      have hd : delete x (.nil : BinaryTree α) = .nil := by simp [delete, hs]
      rw [hc, hd]
      simp only [potential, BinaryTree.numNodes, Nat.cast_zero, Real.logb_zero]
      norm_num
  | node a l r =>
      by_cases hxa : x = a
      · cases hmax : splayMax l with
        | nil =>
            have hl : l = .nil := splayMax_eq_nil.mp hmax
            subst hl
            rw [delete_eq_of_eq_nil hs hxa hmax, costDelete_eq_of_eq hs hxa]
            have hcostMax : costMax (.nil : BinaryTree α) = 1 := by
              simp [costMax, rotationsMax]
            rw [hcostMax]
            push_cast
            have hps := potential_splay_eq_of_eq hs
            simp only [potential] at hps
            have h1 := amortized_cost_le x t
            have hlog := lg_nonneg t.numNodes
            linarith
        | node m l' D =>
            have hps := potential_splay_eq_of_eq hs
            obtain ⟨hD, -⟩ := splayMax_eq_node hmax
            subst hD
            have hpm := potential_splayMax_eq_of_eq_node hmax
            simp only [potential] at hpm
            have hpd := potential_delete_eq_of_eq_node hs hxa hmax
            have hsOrd : BinarySearchTree.Ordered (.node a l r) := by
              rw [← hs]
              exact ordered_splay (x := x) hOrd
            obtain ⟨hOrdL, -, -, -⟩ := hsOrd
            have h1 := amortized_cost_le x t
            have h2 := amortized_splayMax_le l hOrdL
            rw [costDelete_eq_of_eq hs hxa]
            push_cast
            have hlog1 : Real.logb 2 (((t.numNodes - 1 : ℕ) : ℝ)) ≤
                Real.logb 2 (t.numNodes : ℝ) :=
              logb_mono_zero (Nat.sub_le _ _)
            have hlog2 : Real.logb 2 (l.numNodes : ℝ) ≤
                Real.logb 2 (t.numNodes : ℝ) := by
              apply logb_mono_zero
              have hnum : (BinaryTree.node a l r).numNodes = t.numNodes := by
                rw [← hs]
                exact numNodes_splay
              simp only [BinaryTree.numNodes] at hnum
              omega
            have hlogL := lg_nonneg l.numNodes
            have hlogT := lg_nonneg t.numNodes
            linarith
      · rw [delete_eq_of_ne hs hxa, costDelete_eq_of_ne hs hxa]
        have h1 := amortized_cost_le x t
        rw [hs] at h1
        have hlog := lg_nonneg t.numNodes
        linarith

/-- **Amortized cost of the book's insert is at most `4 log₂ n + 2`.** Inserting into an
`n`-node tree costs, in the amortized sense, at most `4 log₂ n + 2` in this file's
rotation-based cost model (rotations, or 1 if none; `potential` sums `log₂` of
subtree sizes): the splay contributes at most `3 log₂ n + 1`, and the new root adds
at most `log₂ n + 1` of potential (the new subtree of the old root contributes at
most `log₂ n`, and the new tree is at most one node larger). No search-tree
ordering is needed. This is the repo's analogue of the FDSA/AFP `A_insert` bound,
not FDSA's statement: AFP's `amor_insert` proves `4 * log 2 (size1 t) + 2` in AFP's
own time-function and potential model. -/
public theorem amortized_nipkowInsert_le [LinearOrder α] (x : α) (t : BinaryTree α) :
    (costInsert x t : ℝ) + potential (nipkowInsert x t) - potential t ≤
      4 * Real.logb 2 (t.numNodes : ℝ) + 2 := by
  simp only [costInsert]
  cases hs : splay x t with
  | nil =>
      have ht : t = .nil := splay_eq_nil.mp hs
      subst ht
      rw [nipkowInsert_eq_of_nil hs]
      have hc : cost x (.nil : BinaryTree α) = 1 := by simp [cost, rotations]
      have hp : potential (.node x .nil .nil : BinaryTree α) = 0 := by
        simp [potential, BinaryTree.numNodes, Real.logb_one]
      rw [hc, hp]
      simp only [potential, BinaryTree.numNodes, Nat.cast_zero, Real.logb_zero]
      norm_num
  | node a l r =>
      have hps := potential_splay_eq_of_eq hs
      have h1 := amortized_cost_le x t
      have hnum : (BinaryTree.node a l r).numNodes = t.numNodes := by
        rw [← hs]
        exact numNodes_splay
      have ht : t.numNodes = l.numNodes + r.numNodes + 1 := by
        simp only [BinaryTree.numNodes] at hnum
        omega
      have hlogT := lg_nonneg t.numNodes
      rcases lt_trichotomy x a with hxa | hxa | hxa
      · rw [nipkowInsert_eq_of_lt hs hxa]
        have hnumR : (BinaryTree.node a .nil r).numNodes = r.numNodes + 1 := by
          simp [BinaryTree.numNodes]
        have hnumN : (BinaryTree.node x l (.node a .nil r)).numNodes = t.numNodes + 1 := by
          simp only [BinaryTree.numNodes]
          omega
        have hpot : potential (.node x l (.node a .nil r) : BinaryTree α) =
            potential l + (potential r + Real.logb 2 ((r.numNodes + 1 : ℕ) : ℝ)) +
              Real.logb 2 (((t.numNodes + 1 : ℕ) : ℝ)) := by
          simp only [potential, hnumR, hnumN, zero_add]
        have hlog1 : Real.logb 2 ((r.numNodes + 1 : ℕ) : ℝ) ≤
            Real.logb 2 (t.numNodes : ℝ) := by
          apply logb_mono_zero
          omega
        have hlog2 : Real.logb 2 (((t.numNodes + 1 : ℕ) : ℝ)) ≤
            Real.logb 2 (t.numNodes : ℝ) + 1 := by
          apply logb_succ_le
          omega
        linarith
      · rw [nipkowInsert_eq_of_eq hs hxa, ← hs]
        linarith
      · rw [nipkowInsert_eq_of_gt hs hxa]
        have hnumL : (BinaryTree.node a l .nil).numNodes = l.numNodes + 1 := by
          simp [BinaryTree.numNodes]
        have hnumN : (BinaryTree.node x (.node a l .nil) r).numNodes = t.numNodes + 1 := by
          simp only [BinaryTree.numNodes]
          omega
        have hpot : potential (.node x (.node a l .nil) r : BinaryTree α) =
            (potential l + Real.logb 2 ((l.numNodes + 1 : ℕ) : ℝ)) + potential r +
              Real.logb 2 (((t.numNodes + 1 : ℕ) : ℝ)) := by
          simp only [potential, hnumL, hnumN, add_zero]
        have hlog1 : Real.logb 2 ((l.numNodes + 1 : ℕ) : ℝ) ≤
            Real.logb 2 (t.numNodes : ℝ) := by
          apply logb_mono_zero
          omega
        have hlog2 : Real.logb 2 (((t.numNodes + 1 : ℕ) : ℝ)) ≤
            Real.logb 2 (t.numNodes : ℝ) + 1 := by
          apply logb_succ_le
          omega
        linarith

section Weighted

variable [LinearOrder α]

omit [LinearOrder α] in
private theorem mem_node_iff {x k : α} {l r : BinaryTree α} :
    x ∈ BinaryTree.node k l r ↔ x ∈ l ∨ x = k ∨ x ∈ r :=
  Iff.rfl

/-- **In a search tree the search for a present key ends at its node.** If `t` is a binary search
tree containing `x`, the subtree `focus x t` at the end of the search path is rooted at a node
holding `x`. -/
theorem focus_eq_node_of_mem {x : α} :
    ∀ {t : BinaryTree α}, BinarySearchTree.Ordered t → x ∈ t → ∃ l r, focus x t = .node x l r
  | .nil, _, hx => False.elim hx
  | .node k l r, hord, hx => by
      obtain ⟨hl, hr, hlk, hkr⟩ := hord
      rcases mem_node_iff.mp hx with hxl | rfl | hxr
      · have hxk : x < k := (BinarySearchTree.all_iff_forall_mem.mp hlk) x hxl
        cases l with
        | nil => exact False.elim hxl
        | node a b c =>
            obtain ⟨l', r', h⟩ := focus_eq_node_of_mem hl hxl
            refine ⟨l', r', ?_⟩
            have hf : focus x (.node k (.node a b c) r) = focus x (.node a b c) := by
              simp [focus, hxk.ne, hxk]
            rw [hf]
            exact h
      · exact ⟨l, r, by simp [focus]⟩
      · have hkx : k < x := (BinarySearchTree.all_iff_forall_mem.mp hkr) x hxr
        cases r with
        | nil => exact False.elim hxr
        | node a b c =>
            obtain ⟨l', r', h⟩ := focus_eq_node_of_mem hr hxr
            refine ⟨l', r', ?_⟩
            have hf : focus x (.node k l (.node a b c)) = focus x (.node a b c) := by
              simp [focus, hkx.ne', not_lt.mpr hkx.le]
            rw [hf]
            exact h

/-- **Amortized cost of accessing a present key.** For positive weights and a search tree `t`
containing `x`, the amortized cost of splaying `t` at `x` is at most `3 (log₂ W(t) - log₂ w(x)) + 1`
(Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985), Lemma 1,
`3 (r(t) - r(x)) + 1 = O(log (s(t) / s(x)))`, with `s(x) ≥ w(x)`). -/
theorem amortized_cost_le_weighted {w : α → ℝ} (hw : ∀ a, 0 < w a) {x : α} {t : BinaryTree α}
    (hord : BinarySearchTree.Ordered t) (hx : x ∈ t) :
    (cost x t : ℝ) + potentialW w (splay x t) - potentialW w t ≤
      3 * (Real.logb 2 (weight w t) - Real.logb 2 (w x)) + 1 := by
  have h := access_lemma_weighted hw x t
  obtain ⟨l, r, hf⟩ := focus_eq_node_of_mem hord hx
  have hle : Real.logb 2 (w x) ≤ Real.logb 2 (weight w (focus x t)) := by
    rw [hf]
    apply lgR_mono (hw x)
    have := weight_nonneg hw l
    have := weight_nonneg hw r
    simp only [weight]
    linarith
  linarith

omit [LinearOrder α] in
theorem sum_logb_le_potentialW {w : α → ℝ} (hw : ∀ a, 0 < w a) : ∀ t : BinaryTree α,
    ((BinarySearchTree.inorder t).map (fun i => Real.logb 2 (w i))).sum ≤ potentialW w t
  | .nil => by simp [BinarySearchTree.inorder, BinarySearchTree.inorderAux, potentialW]
  | .node k l r => by
      have hl := sum_logb_le_potentialW hw l
      have hr := sum_logb_le_potentialW hw r
      have hk : Real.logb 2 (w k) ≤ Real.logb 2 (weight w (.node k l r)) := by
        apply lgR_mono (hw k)
        have := weight_nonneg hw l
        have := weight_nonneg hw r
        simp only [weight]
        linarith
      rw [BinarySearchTree.inorder_node, potentialW]
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      linarith

omit [LinearOrder α] in
theorem potentialW_le_card_mul {w : α → ℝ} (hw : ∀ a, 0 < w a) : ∀ t : BinaryTree α,
    potentialW w t ≤ (t.numNodes : ℝ) * Real.logb 2 (weight w t)
  | .nil => by simp [potentialW]
  | .node k l r => by
      have hl := potentialW_le_card_mul hw l
      have hr := potentialW_le_card_mul hw r
      have hT : 0 < weight w (.node k l r) := weight_node_pos hw k l r
      have hlT : (l.numNodes : ℝ) * Real.logb 2 (weight w l) ≤
          l.numNodes * Real.logb 2 (weight w (.node k l r)) := by
        cases l with
        | nil => simp
        | node a b c =>
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply lgR_mono (weight_node_pos hw a b c)
            have := weight_nonneg hw r
            have := hw k
            simp only [weight] at *
            linarith
      have hrT : (r.numNodes : ℝ) * Real.logb 2 (weight w r) ≤
          r.numNodes * Real.logb 2 (weight w (.node k l r)) := by
        cases r with
        | nil => simp
        | node a b c =>
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply lgR_mono (weight_node_pos hw a b c)
            have := weight_nonneg hw l
            have := hw k
            simp only [weight] at *
            linarith
      rw [potentialW]
      push_cast [BinaryTree.numNodes]
      nlinarith

theorem inorder_splayRun (xs : ℕ → α) (t : BinaryTree α) :
    ∀ i, BinarySearchTree.inorder (splayRun xs t i) = BinarySearchTree.inorder t
  | 0 => rfl
  | i + 1 => by rw [splayRun, inorder_splay, inorder_splayRun xs t i]

theorem ordered_splayRun (xs : ℕ → α) {t : BinaryTree α} (h : BinarySearchTree.Ordered t) :
    ∀ i, BinarySearchTree.Ordered (splayRun xs t i)
  | 0 => h
  | i + 1 => ordered_splay (ordered_splayRun xs h i)

theorem weight_splayRun (w : α → ℝ) (xs : ℕ → α) (t : BinaryTree α) :
    ∀ i, weight w (splayRun xs t i) = weight w t
  | 0 => rfl
  | i + 1 => by rw [splayRun, weight_splay, weight_splayRun w xs t i]

/-- **Splay-tree access bound for arbitrary weights.** For positive item weights `w`, a search
tree `t` of total weight `W` and keys `x₀, …, x_{m-1}` of `t`, the total cost of splaying
successively at them is at most
`∑_j (3 log₂ (W / w(x_j)) + 1) + ∑_{i ∈ t} log₂ (W / w(i))`: each access has amortized cost at
most `3 log₂ (W / w(x_j)) + 1`, and the potential drops by at most `∑_i log₂ (W / w(i))` since
the subtree at the node holding `i` has weight between `w(i)` and `W` (Sleator and Tarjan,
*Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2, the remark before Theorem 1;
Theorems 1–3 are its instances). -/
theorem access_sequence_le_weighted {w : α → ℝ} (hw : ∀ a, 0 < w a) (xs : ℕ → α)
    {t : BinaryTree α} (hord : BinarySearchTree.Ordered t) (m : ℕ)
    (hmem : ∀ j < m, xs j ∈ t) :
    (∑ j ∈ Finset.range m, (cost (xs j) (splayRun xs t j) : ℝ)) ≤
      ∑ j ∈ Finset.range m, (3 * (Real.logb 2 (weight w t) - Real.logb 2 (w (xs j))) + 1) +
        ((BinarySearchTree.inorder t).map
          (fun i => Real.logb 2 (weight w t) - Real.logb 2 (w i))).sum := by
  have key := PotentialMethod.sum_cost_le_of_amortizedCost_le (potentialW w) (splayRun xs t)
    (fun j => (cost (xs j) (splayRun xs t j) : ℝ))
    (fun j => 3 * (Real.logb 2 (weight w t) - Real.logb 2 (w (xs j))) + 1) m (by
      intro j hj
      have hx : xs j ∈ splayRun xs t j := by
        rw [← BinarySearchTree.mem_inorder, inorder_splayRun, BinarySearchTree.mem_inorder]
        exact hmem j hj
      have h := amortized_cost_le_weighted hw (ordered_splayRun xs hord j) hx
      rw [weight_splayRun] at h
      simpa [PotentialMethod.amortizedCost, splayRun] using h)
  have h0 : potentialW w (splayRun xs t 0) ≤
      ((BinarySearchTree.inorder t).map (fun _ => Real.logb 2 (weight w t))).sum := by
    have := potentialW_le_card_mul hw t
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul]
    rw [← BinarySearchTree.numNodes_eq_length_inorder]
    exact this
  have hm := sum_logb_le_potentialW hw (splayRun xs t m)
  rw [inorder_splayRun] at hm
  have hsplit : ((BinarySearchTree.inorder t).map
      (fun i => Real.logb 2 (weight w t) - Real.logb 2 (w i))).sum =
      ((BinarySearchTree.inorder t).map (fun _ => Real.logb 2 (weight w t))).sum -
        ((BinarySearchTree.inorder t).map (fun i => Real.logb 2 (w i))).sum := by
    induction BinarySearchTree.inorder t with
    | nil => simp
    | cons a l ih =>
        simp only [List.map_cons, List.sum_cons] at ih ⊢
        rw [ih]
        ring
  rw [hsplit]
  linarith

/-- **Access frequency.** The number of indices `j < m` with `xs j = i`, the `q(i)` of Sleator and
Tarjan (*Self-adjusting binary search trees*, J. ACM 32(3) (1985), §2). -/
def accessCount (xs : ℕ → α) (m : ℕ) (i : α) : ℕ :=
  ((Finset.range m).filter (fun j => xs j = i)).card

private theorem sum_range_eq_sum_inorder (xs : ℕ → α) {t : BinaryTree α}
    (hord : BinarySearchTree.Ordered t) (m : ℕ) (hmem : ∀ j < m, xs j ∈ t) (F : α → ℝ) :
    ∑ j ∈ Finset.range m, F (xs j) =
      ((BinarySearchTree.inorder t).map (fun i => (accessCount xs m i : ℝ) * F i)).sum := by
  have hnd : (BinarySearchTree.inorder t).Nodup :=
    (BinarySearchTree.ordered_inorder hord).imp (fun h => ne_of_lt h)
  have hmaps : ∀ j ∈ Finset.range m, xs j ∈ (BinarySearchTree.inorder t).toFinset := by
    intro j hj
    rw [List.mem_toFinset, BinarySearchTree.mem_inorder]
    exact hmem j (Finset.mem_range.mp hj)
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps, ← List.sum_toFinset _ hnd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

omit [LinearOrder α] in
private theorem list_sum_aux (l : List α) (q a : α → ℝ) :
    (l.map (fun i => q i * (3 * a i + 1))).sum =
      (l.map (fun i => q i * 1)).sum + 3 * (l.map (fun i => q i * a i)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

/-- **Static optimality of splay trees.** Let `t` be a search tree and `x₀, …, x_{m-1}` keys of
`t` such that every key of `t` is accessed, `q(i) ≥ 1` times. Then splaying successively at
`x₀, …, x_{m-1}` costs in total at most
`m + 3 ∑_{i ∈ t} q(i) log₂ (m / q(i)) + ∑_{i ∈ t} log₂ (m / q(i))`, which is
`O(m + ∑_i q(i) log (m / q(i)))`: within a constant factor of the cost of a static optimum
search tree for these frequencies (Sleator and Tarjan, *Self-adjusting binary search trees*,
J. ACM 32(3) (1985), §2, Theorem 2 (Static Optimality Theorem), proved as there by choosing the
weights `w(i) = q(i)`). -/
theorem static_optimality (xs : ℕ → α) {t : BinaryTree α} (hord : BinarySearchTree.Ordered t)
    (m : ℕ) (hmem : ∀ j < m, xs j ∈ t) (hall : ∀ i ∈ t, 1 ≤ accessCount xs m i) :
    (∑ j ∈ Finset.range m, (cost (xs j) (splayRun xs t j) : ℝ)) ≤
      m + 3 * ((BinarySearchTree.inorder t).map (fun i => (accessCount xs m i : ℝ) *
          (Real.logb 2 m - Real.logb 2 (accessCount xs m i)))).sum +
        ((BinarySearchTree.inorder t).map
          (fun i => Real.logb 2 m - Real.logb 2 (accessCount xs m i))).sum := by
  classical
  set q := accessCount xs m with hq
  let w : α → ℝ := fun i => if q i = 0 then 1 else (q i : ℝ)
  have hw : ∀ a, 0 < w a := by
    intro a
    by_cases h : q a = 0
    · simp [w, h]
    · simp only [w, ite_eq_right h]
      exact_mod_cast Nat.pos_of_ne_zero h
  have hwq : ∀ i ∈ t, w i = q i := by
    intro i hi
    have := hall i hi
    simp only [w, ite_eq_right (by omega : q i ≠ 0)]
  have hWm : weight w t = m := by
    rw [weight_eq_sum_inorder]
    have h1 : ((BinarySearchTree.inorder t).map w).sum =
        ((BinarySearchTree.inorder t).map (fun i => (q i : ℝ) * 1)).sum := by
      congr 1
      refine List.map_congr_left fun i hi => ?_
      rw [mul_one]
      exact hwq i (BinarySearchTree.mem_inorder.mp hi)
    rw [h1, ← sum_range_eq_sum_inorder xs hord m hmem (fun _ => 1)]
    simp
  have key := access_sequence_le_weighted hw xs hord m hmem
  rw [hWm] at key
  have hF : ∀ F : ℝ → ℝ, ((BinarySearchTree.inorder t).map (fun i => F (w i))).sum =
      ((BinarySearchTree.inorder t).map (fun i => F (q i : ℝ))).sum := by
    intro F
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [hwq i (BinarySearchTree.mem_inorder.mp hi)]
  have hsum : ∑ j ∈ Finset.range m, (3 * (Real.logb 2 m - Real.logb 2 (w (xs j))) + 1) =
      m + 3 * ((BinarySearchTree.inorder t).map (fun i => (q i : ℝ) *
          (Real.logb 2 m - Real.logb 2 (q i)))).sum := by
    rw [sum_range_eq_sum_inorder xs hord m hmem
      (fun i => 3 * (Real.logb 2 m - Real.logb 2 (w i)) + 1)]
    have h2 : ((BinarySearchTree.inorder t).map (fun i => (q i : ℝ) *
        (3 * (Real.logb 2 m - Real.logb 2 (w i)) + 1))).sum =
        ((BinarySearchTree.inorder t).map (fun i => (q i : ℝ) *
          (3 * (Real.logb 2 m - Real.logb 2 (q i)) + 1))).sum := by
      congr 1
      refine List.map_congr_left fun i hi => ?_
      rw [hwq i (BinarySearchTree.mem_inorder.mp hi)]
    rw [h2]
    have h3 : (m : ℝ) = ((BinarySearchTree.inorder t).map (fun i => (q i : ℝ) * 1)).sum := by
      rw [← sum_range_eq_sum_inorder xs hord m hmem (fun _ => 1)]
      simp
    rw [list_sum_aux (BinarySearchTree.inorder t) (fun i => (q i : ℝ))
      (fun i => Real.logb 2 m - Real.logb 2 (q i))]
    linarith
  rw [hsum, hF (fun z => Real.logb 2 m - Real.logb 2 z)] at key
  exact key

end Weighted

end SplayTree
end Cslib.Algorithms.Lean
