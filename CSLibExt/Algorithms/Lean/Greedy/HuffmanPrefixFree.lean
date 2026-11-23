/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.HuffmanOptimality
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Comparable

/-!
# Huffman coding against arbitrary prefix-free codes

`huffman_optimal` compares the tree returned by `huffman` only with other `HuffmanTree`s whose
leaves are the input's weighted symbols, and every such tree is full. This file compares that tree
with every binary code `code : α → List Bool` that is prefix-free on the input's symbols in the
sense of `MathlibExt.InformationTheory.IsPrefixFree`. The cost of such a code is the sum of
`weight * (code symbol).length` over the input; codewords of symbols outside the input are
ignored.

The proof builds the code trie of the input's codewords and contracts every node that has a
single child. Contraction only shortens codewords, and the contracted trie is a full tree whose
weighted leaves are a permutation of the input, so `huffman_optimal` applies to it. This is the
argument behind the observation in CLRS, *Introduction to Algorithms*, third edition,
Section 16.3, that an optimal prefix code is always represented by a full binary tree.

## Main results

* `huffman_optimal_prefixFree`: the weighted path length of the tree returned by `huffman` is at
  most the cost of every code that is prefix-free on the input's symbols.
* `huffman_encodedLength_optimal_prefixFree`: the same bound for `HuffmanTree.encodedLength`, for
  every code that is prefix-free on the input's symbols and gives each input symbol of positive
  weight a nonempty codeword. The extra hypothesis matters only for a one-symbol input of positive
  weight: the encoder then spends one bit (`[false]`), while the empty codeword is prefix-free and
  costs zero.
* `HuffmanTree.exists_admissible_of_prefixFree`: the code-to-tree bridge. For a nonempty input
  with distinct symbols and a code that is prefix-free on the input's symbols, some full tree with
  exactly the input's weighted symbols has weighted path length at most the cost of the code.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

open scoped Function

namespace HuffmanPrefixFree

/-- A weighted symbol paired with a binary codeword. -/
private abbrev Entry (α : Type u) := (α × Nat) × List Bool

variable {α : Type u}

/-- Keep an entry whose codeword starts with `bit`, and remove that first bit. -/
private def branch (bit : Bool) (x : Entry α) : Option (Entry α) :=
  match x.2 with
  | b :: bits => if b = bit then some (x.1, bits) else none
  | [] => none

/-- The weighted codeword length of a list of entries. -/
private def cost (entries : List (Entry α)) : Nat :=
  (entries.map fun x => x.1.2 * x.2.length).sum

/-- The total weight of a list of entries. -/
private def weight (entries : List (Entry α)) : Nat :=
  (entries.map fun x => x.1.2).sum

private theorem branch_eq_some {bit : Bool} {x y : Entry α} (h : branch bit x = some y) :
    x.2 = bit :: y.2 := by
  rcases x with ⟨p, _ | ⟨b, bits⟩⟩
  · simp [branch] at h
  · by_cases hb : b = bit
    · subst hb
      simp only [branch, ↓reduceIte, Option.some.injEq] at h
      subst h
      rfl
    · simp [branch, hb] at h

private theorem totalWeight_eq_weight {tree : HuffmanTree α} {entries : List (Entry α)}
    (h : tree.weightedLeaves.Perm (entries.map Prod.fst)) :
    tree.totalWeight = weight entries := by
  rw [← HuffmanTree.sum_snd_weightedLeaves, (h.map Prod.snd).sum_eq, List.map_map]
  rfl

/-- With nonempty codewords, splitting by the first bit keeps every weighted symbol. -/
private theorem perm_branches {entries : List (Entry α)} (hne : ∀ x ∈ entries, x.2 ≠ []) :
    (entries.map Prod.fst).Perm ((entries.filterMap (branch false)).map Prod.fst ++
      (entries.filterMap (branch true)).map Prod.fst) := by
  induction entries with
  | nil => simp
  | cons x entries ih =>
      have ih := ih fun y hy => hne y (List.mem_cons_of_mem _ hy)
      rcases x with ⟨p, _ | ⟨b, bits⟩⟩
      · exact absurd rfl (hne _ List.mem_cons_self)
      · cases b with
        | false => simpa [branch, List.filterMap_cons] using ih
        | true =>
            simpa [branch, List.filterMap_cons] using (ih.cons p).trans List.perm_middle.symm

/-- Splitting by the first bit and removing it lowers the cost by the total weight of the entries
with a nonempty codeword. An entry with the empty codeword costs nothing and is in neither
branch. -/
private theorem cost_branches (entries : List (Entry α)) :
    cost entries =
      cost (entries.filterMap (branch false)) + weight (entries.filterMap (branch false)) +
        (cost (entries.filterMap (branch true)) + weight (entries.filterMap (branch true))) := by
  induction entries with
  | nil => simp [cost, weight]
  | cons x entries ih =>
      rcases x with ⟨p, _ | ⟨b, bits⟩⟩
      · simp only [cost, weight, branch, List.filterMap_cons, List.map_cons, List.sum_cons,
          List.length_nil, Nat.mul_zero, Nat.zero_add] at ih ⊢
        exact ih
      · cases b with
        | false =>
            simp only [cost, weight, branch, List.filterMap_cons, Bool.false_eq_true,
              ↓reduceIte, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at ih ⊢
            omega
        | true =>
            simp only [cost, weight, branch, List.filterMap_cons, Bool.true_eq_false,
              ↓reduceIte, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at ih ⊢
            omega

private theorem pairwise_branch (bit : Bool) {entries : List (Entry α)}
    (h : entries.Pairwise (IncompRel (· <+: ·) on Prod.snd)) :
    (entries.filterMap (branch bit)).Pairwise (IncompRel (· <+: ·) on Prod.snd) := by
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy x' hx' y' hy'
  have hx := branch_eq_some hx'
  have hy := branch_eq_some hy'
  refine ⟨fun hpre => hxy.1 ?_, fun hpre => hxy.2 ?_⟩
  · rw [hx, hy]
    exact (List.prefix_cons_inj bit).mpr hpre
  · rw [hx, hy]
    exact (List.prefix_cons_inj bit).mpr hpre

private theorem length_le_of_mem_branch (bit : Bool) {entries : List (Entry α)} {n : Nat}
    (h : ∀ x ∈ entries, x.2.length ≤ n + 1) :
    ∀ y ∈ entries.filterMap (branch bit), y.2.length ≤ n := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := List.mem_filterMap.mp hy
  have hlen := h x hx
  rw [branch_eq_some hxy, List.length_cons] at hlen
  omega

/-- With two or more pairwise incomparable codewords, none of them is empty. -/
private theorem ne_nil_of_pairwise {x y : Entry α} {rest : List (Entry α)}
    (h : (x :: y :: rest).Pairwise (IncompRel (· <+: ·) on Prod.snd)) :
    ∀ z ∈ x :: y :: rest, z.2 ≠ [] := by
  intro z hz hnil
  rw [List.pairwise_cons] at h
  rcases List.mem_cons.mp hz with rfl | hz
  · exact (h.1 y List.mem_cons_self).1 (by rw [hnil]; exact List.nil_prefix)
  · exact (h.1 z hz).2 (by rw [hnil]; exact List.nil_prefix)

/-- A nonempty list of entries whose codewords are pairwise incomparable and have length at most
`n` is dominated by a full tree: its weighted leaves are a permutation of the entries' weighted
symbols, and its weighted path length is at most their cost. The tree is the code trie with every
single-child node contracted. -/
private theorem exists_tree (n : Nat) :
    ∀ entries : List (Entry α), entries ≠ [] → entries.Pairwise (IncompRel (· <+: ·) on Prod.snd) →
      (∀ x ∈ entries, x.2.length ≤ n) →
      ∃ tree : HuffmanTree α, tree.weightedLeaves.Perm (entries.map Prod.fst) ∧
        tree.weightedPathLength ≤ cost entries := by
  induction n with
  | zero =>
      intro entries hne hpw hlen
      rcases entries with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · exact absurd rfl hne
      · exact ⟨.leaf x.1.1 x.1.2, List.Perm.refl _, Nat.zero_le _⟩
      · exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen x List.mem_cons_self)))
          (ne_nil_of_pairwise hpw x List.mem_cons_self)
  | succ n ih =>
      intro entries hne hpw hlen
      rcases entries with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · exact absurd rfl hne
      · exact ⟨.leaf x.1.1 x.1.2, List.Perm.refl _, Nat.zero_le _⟩
      · have hnil := ne_nil_of_pairwise hpw
        have hperm := perm_branches hnil
        have hcost := cost_branches (x :: y :: rest)
        have hpw0 := pairwise_branch false hpw
        have hpw1 := pairwise_branch true hpw
        have hlen0 := length_le_of_mem_branch false hlen
        have hlen1 := length_le_of_mem_branch true hlen
        generalize (x :: y :: rest).filterMap (branch false) = left at hperm hcost hpw0 hlen0
        generalize (x :: y :: rest).filterMap (branch true) = right at hperm hcost hpw1 hlen1
        by_cases hleft : left = []
        · subst hleft
          by_cases hright : right = []
          · subst hright
            simp at hperm
          · -- Every codeword starts with `true`: contract the unary root.
            obtain ⟨rightTree, hpermRight, hcostRight⟩ := ih right hright hpw1 hlen1
            refine ⟨rightTree, hpermRight.trans hperm.symm, ?_⟩
            rw [hcost]
            omega
        · obtain ⟨leftTree, hpermLeft, hcostLeft⟩ := ih left hleft hpw0 hlen0
          by_cases hright : right = []
          · -- Every codeword starts with `false`: contract the unary root.
            subst hright
            simp only [List.map_nil, List.append_nil] at hperm
            refine ⟨leftTree, hpermLeft.trans hperm.symm, ?_⟩
            rw [hcost]
            omega
          · obtain ⟨rightTree, hpermRight, hcostRight⟩ := ih right hright hpw1 hlen1
            refine ⟨.fork leftTree rightTree, (hpermLeft.append hpermRight).trans hperm.symm, ?_⟩
            rw [HuffmanTree.weightedPathLength_fork, totalWeight_eq_weight hpermLeft,
              totalWeight_eq_weight hpermRight, hcost]
            omega

end HuffmanPrefixFree

open HuffmanPrefixFree in
/-- The tree returned by `huffman` has weighted path length at most the cost
`Σ weight * (code symbol).length`, summed over `input`, of every binary code that is prefix-free
on the input's symbols. Codewords of symbols outside the input are unconstrained, so this covers
in particular every code that is prefix-free on all of `α`. No codeword needs to be nonempty: for
a one-symbol input the weighted path length is zero. -/
theorem huffman_optimal_prefixFree {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree : HuffmanTree α} {code : α → List Bool}
    (hresult : huffman input = some tree)
    (hcode : MathlibExt.InformationTheory.IsPrefixFree
      fun symbol : {a // a ∈ input.map Prod.fst} => code symbol.1) :
    tree.weightedPathLength ≤ (input.map fun pair => pair.2 * (code pair.1).length).sum := by
  have hne : input ≠ [] := by
    rintro rfl
    simp [huffman] at hresult
  have hnd : (input.map Prod.fst).Nodup := by
    by_contra hdup
    have hnone := huffman_eq_none_iff.mpr (Or.inr hdup)
    rw [hresult] at hnone
    cases hnone
  let entries : List (Entry α) := input.map fun pair => (pair, code pair.1)
  have hfst : entries.map Prod.fst = input := by
    simp only [entries, List.map_map]
    exact List.map_id input
  have hpw : entries.Pairwise (IncompRel (· <+: ·) on Prod.snd) := by
    rw [List.pairwise_map]
    refine (List.pairwise_map.mp hnd).imp_of_mem ?_
    intro p q hp hq hpq
    have hp' : p.1 ∈ input.map Prod.fst := List.mem_map_of_mem hp
    have hq' : q.1 ∈ input.map Prod.fst := List.mem_map_of_mem hq
    exact ⟨hcode (a₁ := ⟨p.1, hp'⟩) (a₂ := ⟨q.1, hq'⟩)
        fun h => hpq (congrArg Subtype.val h),
      hcode (a₁ := ⟨q.1, hq'⟩) (a₂ := ⟨p.1, hp'⟩)
        fun h => hpq (congrArg Subtype.val h).symm⟩
  obtain ⟨competitor, hperm, hcost⟩ :=
    exists_tree (entries.map fun x => x.2.length).sum entries
      (fun h => hne (List.map_eq_nil_iff.mp h)) hpw
      fun x hx => List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : Entry α => x.2.length) hx)
  have hadmissible : competitor.Admissible input := by
    rw [← hfst]
    exact hperm
  calc tree.weightedPathLength ≤ competitor.weightedPathLength :=
        huffman_optimal hresult hadmissible
    _ ≤ cost entries := hcost
    _ = (input.map fun pair => pair.2 * (code pair.1).length).sum := by
        simp only [cost, entries, List.map_map]
        rfl

/-- The tree returned by `huffman` has `encodedLength` at most the cost
`Σ weight * (code symbol).length`, summed over `input`, of every binary code that is prefix-free
on the input's symbols and gives each input symbol of positive weight a nonempty codeword. That
hypothesis matters only for a one-symbol input of positive weight, where the bound fails for the
empty codeword: `encodedLength` charges the encoder's one-bit codeword `[false]`, while the empty
codeword is prefix-free on one symbol and costs zero. A one-symbol input of weight zero needs no
nonempty codeword, since both sides are zero, and with two or more distinct input symbols
prefix-freeness already makes every input codeword nonempty.
`HuffmanTree.encodedLength_eq_sum_codeLengths` states when `encodedLength` is the encoder's
emitted cost. -/
theorem huffman_encodedLength_optimal_prefixFree {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree : HuffmanTree α} {code : α → List Bool}
    (hresult : huffman input = some tree)
    (hcode : MathlibExt.InformationTheory.IsPrefixFree
      fun symbol : {a // a ∈ input.map Prod.fst} => code symbol.1)
    (hnonempty : ∀ pair ∈ input, 0 < pair.2 → code pair.1 ≠ []) :
    tree.encodedLength ≤ (input.map fun pair => pair.2 * (code pair.1).length).sum := by
  cases tree with
  | leaf symbol weight =>
      have hinput : input = [(symbol, weight)] :=
        List.perm_singleton.mp (huffman_weightedLeaves_perm hresult).symm
      subst hinput
      rcases Nat.eq_zero_or_pos weight with hzero | hpos
      · subst hzero
        exact Nat.zero_le _
      · have hlen : 0 < (code symbol).length :=
          List.length_pos_iff.mpr (hnonempty (symbol, weight) List.mem_cons_self hpos)
        simpa [HuffmanTree.encodedLength] using Nat.le_mul_of_pos_right weight hlen
  | fork left right =>
      rw [HuffmanTree.encodedLength_fork]
      exact huffman_optimal_prefixFree hresult hcode

/-- Code-to-tree bridge: for a nonempty input with distinct symbols and a binary code that is
prefix-free on the input's symbols, some admissible tree (a full tree whose weighted leaves are a
permutation of the input) has weighted path length at most the code's cost
`Σ weight * (code symbol).length`, summed over `input`. The tree returned by `huffman` is one, by
`huffman_optimal_prefixFree`. Codewords of symbols outside the input are unconstrained, and no
codeword needs to be nonempty. -/
theorem HuffmanTree.exists_admissible_of_prefixFree {α : Type u}
    {input : List (α × Nat)} {code : α → List Bool}
    (hne : input ≠ []) (hnd : (input.map Prod.fst).Nodup)
    (hcode : MathlibExt.InformationTheory.IsPrefixFree
      fun symbol : {a // a ∈ input.map Prod.fst} => code symbol.1) :
    ∃ tree : HuffmanTree α, tree.Admissible input ∧
      tree.weightedPathLength ≤ (input.map fun pair => pair.2 * (code pair.1).length).sum := by
  classical
  obtain ⟨tree, hresult⟩ := Option.isSome_iff_exists.mp (huffman_isSome hne hnd)
  exact ⟨tree, huffman_weightedLeaves_perm hresult, huffman_optimal_prefixFree hresult hcode⟩

end Cslib.Algorithms.Lean
