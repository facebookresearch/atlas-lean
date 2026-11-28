/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.List2
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Tree
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Framework
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.LogLemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic

/-!
# Pairing heaps: amortized analysis (book §23.2, §23.3)

The potential-method analysis for the pairing-heap variants: the `sz`
size function and `Φ` potential for the book version (`List2`), with
`ΔΦ_link`, `ΔΦ_insert`, Lemma 23.2 (`ΔΦ_pass1`), Lemma 23.3
(`ΔΦ_pass2`), Corollary 23.4, Theorem 23.1 (`ΔΦ_delMin`), and the three
amortized bounds `A_insert` / `A_merge` / `A_delMin`; the `trees`
representation of heaps as binary trees (§23.3), with `sz` / `Φ` as tree
size / potential; and the simplified analysis for the binary-tree
variant (`Tree`): `len`, the `ΔΦ` lemmas, the `T_*` functions, the `A_*`
bounds. Both variants are packaged as `AmortizedData` instances over
the shared operation type `Op` (`Priority_Queue_ops_merge`'s `op`),
so the framework's `t_sum_le_U_sum` applies to each.

This file reuses the shared generic framework (`Amortized.Framework`:
`AmortizedData`, rose-tree histories, `t_sum_le_U_sum`) and the shared
logarithm lemmas (`Amortized.LogLemmas`: `ld_sum_inequality`, …) from
the Chapter 22 work instead of duplicating them; only the small helper
`logb_two_nonneg_of_one_le`, which that module does not provide, is
proved here. The `List2` time functions (`Tlink`, `Tinsert`, `Tmerge`,
`Tpass1`, `Tpass2`, `TdelMin`, `TmergePairs`) live in
`PairingHeap.List2`; the `Tree` time functions are defined here, next
to the analysis that uses them.

File order note: the `Tree` section comes first because the `List2`
§23.3 mapping (`phiHp_tree`) refers to `Tree.phiTree`.

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_List2.thy`, `Pairing_Heap_Tree.thy`) and
`Amortized_Complexity` (`Pairing_Heap_List2_Analysis.thy`,
`Pairing_Heap_Tree_Analysis2.thy`, `Amortized_Framework.thy`,
`Lemmas_log.thy`, `Priority_Queue_ops_merge.thy`), and Tobias Nipkow
(ed.), *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, Chapter 23 (Pairing Heaps, pp. 257–264) with Appendix B.11.
Isabelle-derived names are kept for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Algorithms.Lean
namespace PairingHeap

open Cslib.Algorithms.Lean.Amortized

variable {α : Type u}

/-- The operations of the amortized framework
(`Priority_Queue_ops_merge`'s `'a op`). -/
inductive Op (β : Type u) where
  | Empty : Op β
  | Insert : β → Op β
  | DelMin : Op β
  | Merge : Op β

/-- `arity` from `Priority_Queue_ops_merge.thy`. -/
def arityOp : Op α → ℕ
  | .Empty => 0
  | .Insert _ => 1
  | .DelMin => 1
  | .Merge => 2

/-- `0 ≤ log₂ x` for `1 ≤ x`. -/
theorem logb_two_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.logb 2 x :=
  Real.logb_nonneg (by norm_num) hx

namespace Tree

/-- The potential on binary trees (book §23.3): `Φ leaf = 0`,
`Φ ⟨l; x; r⟩ = lg |⟨l; x; r⟩| + Φ l + Φ r`. The summands are written
in the AFP's order (`Pairing_Heap_List1_Analysis1.thy`:
`Φ (Node l x r) = log 2 (size (Node l x r)) + Φ l + Φ r`); addition is
commutative, so this is the same function. -/
noncomputable def phiTree : BTree α → ℝ
  | .leaf => 0
  | .node l x r => Real.logb 2 ((sizeTree (BTree.node l x r) : ℝ)) + phiTree l + phiTree r

theorem phiTree_leaf : phiTree (BTree.leaf : BTree α) = 0 := by simp [phiTree]

theorem phiTree_node (l r : BTree α) (x : α) :
    phiTree (BTree.node l x r) =
      Real.logb 2 ((sizeTree (BTree.node l x r) : ℝ)) + phiTree l + phiTree r := by
  simp [phiTree]

theorem phiTree_nonneg (t : BTree α) : 0 ≤ phiTree t := by
  induction t with
  | leaf => rw [phiTree_leaf]
  | node l x r ihl ihr =>
    rw [phiTree_node]
    have hlog : 0 ≤ Real.logb 2 ((sizeTree (BTree.node l x r) : ℝ)) := by
      apply logb_two_nonneg_of_one_le
      have h1 : (1 : ℕ) ≤ sizeTree (BTree.node l x r) := by
        rw [sizeTree_node]; omega
      exact_mod_cast h1
    linarith

/-! ### Amortized analysis: `Pairing_Heap_Tree_Analysis2.thy` -/

/-- AFP `len`: the length of the right spine of a binary tree. -/
def len : BTree α → ℕ
  | .leaf => 0
  | .node _ _ r => 1 + len r

theorem len_leaf : len (BTree.leaf : BTree α) = 0 := rfl

theorem len_node (l r : BTree α) (x : α) :
    len (.node l x r) = 1 + len r := rfl

/-- AFP `link_size[simp]`: linking preserves size. -/
theorem link_size [LinearOrder α] (hp : BTree α) :
    sizeTree (link hp) = sizeTree hp := by
  cases hp with
  | leaf => rfl
  | node hsx x r =>
    cases r with
    | leaf => rfl
    | node hsy y hs =>
      by_cases hc : x < y
      · rw [link_eq_pos hc]; simp only [sizeTree_node]; omega
      · rw [link_eq_neg hc]; simp only [sizeTree_node]; omega

/-- AFP `size_pass1`: `pass1` preserves size. -/
theorem size_pass1 [LinearOrder α] (hs : BTree α) :
    sizeTree (pass1 hs) = sizeTree hs := by
  induction hs using BTree_ind with
  | step t ih =>
    cases t with
    | leaf => rfl
    | node l x r =>
      cases r with
      | leaf => rfl
      | node m y r' =>
        rw [pass1_cons2, link_size]
        have hlt : sizeTree r' < sizeTree (BTree.node l x (BTree.node m y r')) := by
          simp only [sizeTree_node]; omega
        simp only [sizeTree_node]
        rw [ih r' hlt]

/-- AFP `size_pass2`: `pass2` preserves size. -/
theorem size_pass2 [LinearOrder α] (hs : BTree α) :
    sizeTree (pass2 hs) = sizeTree hs := by
  induction hs with
  | leaf => rfl
  | node l x r ihl ihr =>
    rw [pass2_cons, link_size]
    simp only [sizeTree_node]
    rw [ihr]

/-- AFP `size_merge`: merging roots adds sizes. -/
theorem size_merge [LinearOrder α] {h1 h2 : BTree α} (h1r : isRoot h1)
    (h2r : isRoot h2) :
    sizeTree (merge h1 h2) = sizeTree h1 + sizeTree h2 := by
  cases h1 with
  | leaf =>
    rw [merge_leaf_left]
    simp [sizeTree_leaf]
  | node hsx x rx =>
    cases h2 with
    | leaf =>
      rw [merge_leaf_right]
      simp [sizeTree_leaf]
    | node hsy y ry =>
      rw [isRoot_node] at h1r h2r
      subst h1r
      subst h2r
      rw [merge_node_node, link_size]
      simp only [sizeTree_node, sizeTree_leaf]
      omega

/-- The potential of a `link` of a two-level node: the potentials of the
three subtrees plus the two log terms (the identity the AFP's `ΔΦ_merge`
proof establishes by `simp`). Both comparisons give the same value. -/
theorem phiTree_link [LinearOrder α] (hsx hsy hs : BTree α) (x y : α) :
    phiTree (link (.node hsx x (.node hsy y hs))) =
      phiTree hsx + phiTree hsy + phiTree hs
        + Real.logb 2 ((sizeTree hsx + sizeTree hsy + 1 : ℕ) : ℝ)
        + Real.logb 2 ((sizeTree (.node hsx x (.node hsy y hs)) : ℕ) : ℝ) := by
  by_cases hc : x < y
  · have hsize : sizeTree (.node (.node hsy y hsx) x hs) =
        sizeTree (.node hsx x (.node hsy y hs)) := by
      simp only [sizeTree_node]; omega
    rw [link_eq_pos hc]
    simp only [phiTree_node]
    rw [hsize]
    simp only [sizeTree_node]
    ring_nf
  · have hsize : sizeTree (.node (.node hsx x hsy) y hs) =
        sizeTree (.node hsx x (.node hsy y hs)) := by
      simp only [sizeTree_node]; omega
    rw [link_eq_neg hc]
    simp only [phiTree_node]
    rw [hsize]
    simp only [sizeTree_node]
    ring_nf

/-- AFP `ΔΦ_insert`: inserting increases the potential by at most
`log 2 (size h + 1)`. -/
theorem deltaPhi_insert [LinearOrder α] {hp : BTree α} (x : α)
    (hr : isRoot hp) :
    phiTree (insert x hp) - phiTree hp ≤ Real.logb 2 ((sizeTree hp : ℝ) + 1) := by
  cases hp with
  | leaf =>
    rw [insert_eq, merge_leaf_right]
    simp [phiTree_node, phiTree_leaf, sizeTree_node, sizeTree_leaf]
  | node hs y r =>
    rw [isRoot_node] at hr
    subst hr
    have hEq : phiTree (insert x (.node hs y .leaf)) - phiTree (.node hs y .leaf)
        = Real.logb 2 ((sizeTree hs + 2 : ℕ) : ℝ) := by
      rw [insert_eq, merge_node_node, phiTree_link]
      simp only [phiTree_node, phiTree_leaf, sizeTree_node, sizeTree_leaf]
      ring_nf
    rw [hEq]
    have hsize : (sizeTree (.node hs y .leaf) : ℝ) + 1 = (sizeTree hs + 2 : ℕ) := by
      rw [sizeTree_node, sizeTree_leaf]
      push_cast
      ring
    rw [hsize]

/-- AFP `ΔΦ_merge`: merging two roots increases the potential by at most
`log 2 (size h1 + size h2) + 1` (via `ld_le_2ld`'s argument:
`log (n1 + n2 + 1) ≤ log (n1 + 1) + log (n2 + 1) + 1`, since
`(n1 + 1)(n2 + 1) ≥ n1 + n2 + 1`). -/
theorem deltaPhi_merge [LinearOrder α] {h1 h2 : BTree α} (hs1 hs2 : BTree α)
    (x1 x2 : α) (hh1 : h1 = .node hs1 x1 .leaf)
    (hh2 : h2 = .node hs2 x2 .leaf) :
    phiTree (merge h1 h2) - phiTree h1 - phiTree h2
      ≤ Real.logb 2 ((sizeTree h1 + sizeTree h2 : ℕ) : ℝ) + 1 := by
  subst hh1
  subst hh2
  have hEq : phiTree (merge (.node hs1 x1 .leaf) (.node hs2 x2 .leaf))
      - phiTree (.node hs1 x1 .leaf) - phiTree (.node hs2 x2 .leaf)
      = Real.logb 2 ((sizeTree hs1 + sizeTree hs2 + 1 : ℕ) : ℝ)
        + Real.logb 2 ((sizeTree hs1 + sizeTree hs2 + 2 : ℕ) : ℝ)
        - Real.logb 2 ((sizeTree hs1 + 1 : ℕ) : ℝ)
        - Real.logb 2 ((sizeTree hs2 + 1 : ℕ) : ℝ) := by
    rw [merge_node_node, phiTree_link]
    simp only [phiTree_node, phiTree_leaf, sizeTree_node, sizeTree_leaf]
    ring_nf
  rw [hEq]
  have hsize : (sizeTree (.node hs1 x1 .leaf) + sizeTree (.node hs2 x2 .leaf) : ℕ)
      = sizeTree hs1 + sizeTree hs2 + 2 := by
    simp only [sizeTree_node, sizeTree_leaf]; omega
  have hlog1 : Real.logb 2 ((sizeTree hs1 + sizeTree hs2 + 2 : ℕ) : ℝ)
      = Real.logb 2 ((sizeTree (.node hs1 x1 .leaf) + sizeTree (.node hs2 x2 .leaf) : ℕ) : ℝ) := by
    rw [hsize]
  rw [hlog1]
  have hkey : Real.logb 2 ((sizeTree hs1 + sizeTree hs2 + 1 : ℕ) : ℝ)
      ≤ Real.logb 2 ((sizeTree hs1 + 1 : ℕ) : ℝ)
        + Real.logb 2 ((sizeTree hs2 + 1 : ℕ) : ℝ) + 1 := by
    have hmul : ((sizeTree hs1 + sizeTree hs2 + 1 : ℕ) : ℝ)
        ≤ ((sizeTree hs1 + 1 : ℕ) : ℝ) * ((sizeTree hs2 + 1 : ℕ) : ℝ) := by
      have h := Nat.zero_le (sizeTree hs1 * sizeTree hs2)
      push_cast at h ⊢
      nlinarith [h]
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (Nat.cast_pos.mpr (by omega : (0 : ℕ) < sizeTree hs1 + sizeTree hs2 + 1)) hmul
    rw [Real.logb_mul (by positivity : ((sizeTree hs1 + 1 : ℕ) : ℝ) ≠ 0)
      (by positivity : ((sizeTree hs2 + 1 : ℕ) : ℝ) ≠ 0)] at hlog
    linarith
  linarith

/-- The first step of the AFP's `ΔΦ_pass1` calc: the potential change of
one `pass1` step, in terms of the potential change at the grandchild. -/
theorem phiTree_pass1_diff [LinearOrder α] (hs1 hs2 hs : BTree α) (x y : α) :
    phiTree (pass1 (.node hs1 x (.node hs2 y hs))) - phiTree (.node hs1 x (.node hs2 y hs))
      = phiTree (pass1 hs) + Real.logb 2 ((sizeTree hs1 + sizeTree hs2 + 1 : ℕ) : ℝ)
        - phiTree hs - Real.logb 2 ((sizeTree hs2 + sizeTree hs + 1 : ℕ) : ℝ) := by
  rw [pass1_cons2, phiTree_link]
  have hsize : sizeTree (.node hs1 x (.node hs2 y (pass1 hs)))
      = sizeTree (.node hs1 x (.node hs2 y hs)) := by
    simp only [sizeTree_node]
    rw [size_pass1]
  rw [hsize]
  simp only [phiTree_node, sizeTree_node]
  ring_nf

/-- AFP `ΔΦ_pass1`: `Φ (pass1 hs) − Φ hs ≤ 2·log 2 (size hs + 1) − len hs + 2`.
The AFP proof is a four-step `also have` calc over `logb`; here each step
is a named `have` and the cascade is closed by one `linarith`. -/
theorem deltaPhi_pass1 [LinearOrder α] (hs : BTree α) :
    phiTree (pass1 hs) - phiTree hs
      ≤ 2 * Real.logb 2 ((sizeTree hs : ℝ) + 1) - (len hs : ℝ) + 2 := by
  induction hs using BTree_ind with
  | step t ih =>
    cases t with
    | leaf =>
      rw [pass1_leaf, phiTree_leaf, len_leaf, sizeTree_leaf]
      norm_num [Real.logb_one]
    | node hs1 x r =>
      cases r with
      | leaf =>
        rw [pass1_node_leaf, sub_self]
        have hnonneg : 0 ≤ Real.logb 2 ((sizeTree (.node hs1 x .leaf) : ℝ) + 1) :=
          Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by
            have h0 : (0 : ℝ) ≤ (sizeTree (.node hs1 x .leaf) : ℝ) := by positivity
            linarith)
        have hlen : ((len (.node hs1 x .leaf) : ℕ) : ℝ) = 1 := by
          rw [len_node, len_leaf]; norm_num
        rw [hlen]
        linarith
      | node hs2 y hs =>
        have hlt : sizeTree hs < sizeTree (.node hs1 x (.node hs2 y hs)) := by
          simp only [sizeTree_node]; omega
        have hIH := ih hs hlt
        have hIH' : phiTree (pass1 hs) - phiTree hs
            ≤ 2 * Real.logb 2 ((sizeTree hs + 1 : ℕ) : ℝ) - (len hs : ℝ) + 2 := by
          have hcast : ((sizeTree hs + 1 : ℕ) : ℝ) = (sizeTree hs : ℝ) + 1 := by
            push_cast; ring
          rw [hcast]
          exact hIH
        have hstep := phiTree_pass1_diff hs1 hs2 hs x y
        have hsum := ld_sum_inequality
          (show (0 : ℝ) < ((sizeTree hs1 + sizeTree hs2 + 1 : ℕ) : ℝ) from
            Nat.cast_pos.mpr (by omega))
          (show (0 : ℝ) < ((sizeTree hs + 1 : ℕ) : ℝ) from
            Nat.cast_pos.mpr (by omega))
        have harg : ((sizeTree hs1 + sizeTree hs2 + 1 : ℕ) : ℝ)
            + ((sizeTree hs + 1 : ℕ) : ℝ)
            = ((sizeTree hs1 + sizeTree hs2 + sizeTree hs + 2 : ℕ) : ℝ) := by
          push_cast; ring
        rw [harg] at hsum
        have hmono1 : Real.logb 2 ((sizeTree hs + 1 : ℕ) : ℝ)
            ≤ Real.logb 2 ((sizeTree hs2 + sizeTree hs + 1 : ℕ) : ℝ) :=
          Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            (Nat.cast_pos.mpr (by omega))
            (by push_cast
                have h0 : (0 : ℝ) ≤ (sizeTree hs2 : ℝ) := by positivity
                linarith)
        have hsize : sizeTree (.node hs1 x (.node hs2 y hs))
            = sizeTree hs1 + sizeTree hs2 + sizeTree hs + 2 := by
          simp only [sizeTree_node]; omega
        have hmono2 : Real.logb 2 ((sizeTree hs1 + sizeTree hs2 + sizeTree hs + 2 : ℕ) : ℝ)
            ≤ Real.logb 2 ((sizeTree (.node hs1 x (.node hs2 y hs)) : ℝ) + 1) := by
          apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            (Nat.cast_pos.mpr (by omega))
          rw [hsize]
          push_cast
          have h0 : (0 : ℝ) ≤ (sizeTree hs1 : ℝ) := by positivity
          have h1 : (0 : ℝ) ≤ (sizeTree hs2 : ℝ) := by positivity
          have h2 : (0 : ℝ) ≤ (sizeTree hs : ℝ) := by positivity
          linarith
        have hgoal : (len (.node hs1 x (.node hs2 y hs)) : ℝ) = (len hs : ℝ) + 2 := by
          have hlen : len (.node hs1 x (.node hs2 y hs)) = len hs + 2 := by
            rw [len_node, len_node]; omega
          rw [hlen]; push_cast; ring
        rw [hgoal]
        linarith [hstep, hIH', hsum, hmono1, hmono2]

/-- AFP `ΔΦ_pass2`: for `hs ≠ leaf`,
`Φ (pass2 hs) − Φ hs ≤ log 2 (size hs)`. -/
theorem deltaPhi_pass2 [LinearOrder α] {hs : BTree α} (hne : hs ≠ .leaf) :
    phiTree (pass2 hs) - phiTree hs ≤ Real.logb 2 (sizeTree hs : ℝ) := by
  induction hs using BTree_ind with
  | step t ih =>
    cases t with
    | leaf =>
      exact absurd rfl hne
    | node hs1 x hs' =>
      cases hs' with
      | leaf =>
        rw [pass2_cons, pass2_leaf, link_node_leaf, sub_self]
        apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
        rw [sizeTree_node, sizeTree_leaf]
        push_cast
        have h0 : (0 : ℝ) ≤ (sizeTree hs1 : ℝ) := by positivity
        linarith
      | node hs2 y r =>
        obtain ⟨hs3, a, hpass⟩ := pass2_struct (hs1 := hs2) (x := y) (hs := r)
        have hne' : (BTree.node hs2 y r : BTree α) ≠ BTree.leaf := by simp
        have hlt : sizeTree (.node hs2 y r)
            < sizeTree (.node hs1 x (.node hs2 y r)) := by
          simp only [sizeTree_node]; omega
        have hIH := ih (.node hs2 y r) hlt hne'
        have hsizepass : sizeTree (pass2 (.node hs2 y r)) = sizeTree (.node hs2 y r) :=
          size_pass2 _
        rw [hpass] at hsizepass
        simp only [sizeTree_node, sizeTree_leaf] at hsizepass
        have heq : phiTree (pass2 (.node hs1 x (.node hs2 y r)))
            - phiTree (.node hs1 x (.node hs2 y r))
            = (phiTree (pass2 (.node hs2 y r)) - phiTree (.node hs2 y r))
              + Real.logb 2 ((sizeTree hs1 + sizeTree (.node hs2 y r) : ℕ) : ℝ)
              - Real.logb 2 ((sizeTree (.node hs2 y r) : ℕ) : ℝ) := by
          rw [pass2_cons, hpass, phiTree_link]
          have hsize2 : sizeTree (.node hs1 x (.node hs3 a .leaf))
              = sizeTree (.node hs1 x (.node hs2 y r)) := by
            simp only [sizeTree_node, sizeTree_leaf]
            omega
          rw [hsize2]
          simp only [phiTree_node, phiTree_leaf, sizeTree_node, sizeTree_leaf]
          have hcast : ((sizeTree hs1 + sizeTree hs3 + 1 : ℕ) : ℝ)
              = ((sizeTree hs1 + (sizeTree hs2 + sizeTree r + 1) : ℕ) : ℝ) := by
            exact_mod_cast
              (by omega : sizeTree hs1 + sizeTree hs3 + 1
                = sizeTree hs1 + (sizeTree hs2 + sizeTree r + 1))
          have hcast2 : ((sizeTree hs3 + 0 + 1 : ℕ) : ℝ)
              = ((sizeTree hs2 + sizeTree r + 1 : ℕ) : ℝ) := by
            exact_mod_cast hsizepass
          rw [hcast, hcast2]
          ring_nf
        rw [heq]
        have hpos : (0 : ℝ) < ((sizeTree hs1 + sizeTree (.node hs2 y r) : ℕ) : ℝ) := by
          have h : (0 : ℕ) < sizeTree hs1 + sizeTree (.node hs2 y r) := by
            rw [sizeTree_node]; omega
          exact_mod_cast h
        have hle : ((sizeTree hs1 + sizeTree (.node hs2 y r) : ℕ) : ℝ)
            ≤ ((sizeTree (.node hs1 x (.node hs2 y r)) : ℕ) : ℝ) := by
          have hsizeh : sizeTree (.node hs1 x (.node hs2 y r))
              = sizeTree hs1 + sizeTree (.node hs2 y r) + 1 := by
            simp only [sizeTree_node]
          rw [hsizeh]; push_cast
          have h0 : (0 : ℝ) ≤ (sizeTree hs1 : ℝ) := by positivity
          have h1 : (0 : ℝ) ≤ (sizeTree (.node hs2 y r) : ℝ) := by positivity
          linarith
        have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hle
        linarith [hIH, hmono]

/-- AFP `ΔΦ_pass2'`: the corollary `Φ (pass2 hs) − Φ hs ≤ log 2 (size hs + 1)`
for all `hs` (the `hs = leaf` case is trivial). -/
theorem deltaPhi_pass2' [LinearOrder α] (hs : BTree α) :
    phiTree (pass2 hs) - phiTree hs ≤ Real.logb 2 ((sizeTree hs : ℝ) + 1) := by
  cases hs with
  | leaf =>
    rw [pass2_leaf, phiTree_leaf, sizeTree_leaf]
    norm_num [Real.logb_one]
  | node hs1 x hs' =>
    have h := deltaPhi_pass2 (hs := .node hs1 x hs') (by simp)
    have hmono : Real.logb 2 ((sizeTree (.node hs1 x hs') : ℕ) : ℝ)
        ≤ Real.logb 2 ((sizeTree (.node hs1 x hs') : ℝ) + 1) := by
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (Nat.cast_pos.mpr (by rw [sizeTree_node]; omega))
      have h0 : (0 : ℝ) ≤ (sizeTree (.node hs1 x hs') : ℝ) := by positivity
      linarith
    linarith

/-- AFP `ΔΦ_del_min`: `Φ (del_min (node hs x leaf)) − Φ (node hs x leaf)
≤ 2·log 2 (size hs + 1) − len hs + 2`. -/
theorem deltaPhi_delMin [LinearOrder α] (hs : BTree α) (x : α) :
    phiTree (delMin (.node hs x .leaf)) - phiTree (.node hs x .leaf)
      ≤ 2 * Real.logb 2 ((sizeTree hs : ℝ) + 1) - (len hs : ℝ) + 2 := by
  have hEq : phiTree (pass2 (pass1 hs)) - phiTree (.node hs x .leaf)
      = phiTree (pass2 (pass1 hs)) - (Real.logb 2 ((sizeTree hs : ℝ) + 1) + phiTree hs) := by
    have hsize : (sizeTree (.node hs x .leaf) : ℝ) = (sizeTree hs : ℝ) + 1 := by
      rw [sizeTree_node, sizeTree_leaf]; push_cast; ring
    rw [phiTree_node, hsize]
    simp only [phiTree_leaf, add_zero]
  rw [delMin_node, hEq]
  have h2 := deltaPhi_pass2' (pass1 hs)
  have h3 : sizeTree (pass1 hs) = sizeTree hs := size_pass1 hs
  rw [h3] at h2
  have h4 := deltaPhi_pass1 hs
  linarith

/-- AFP `len_link`: linking does not increase the spine length. -/
theorem len_link [LinearOrder α] (t : BTree α) : len (link t) ≤ len t := by
  cases t with
  | leaf => simp [link_leaf]
  | node hsx x r =>
    cases r with
    | leaf => simp [link_node_leaf]
    | node hsy y hs =>
      by_cases hc : x < y
      · rw [link_eq_pos hc]
        simp only [len_node]; omega
      · rw [link_eq_neg hc]
        simp only [len_node]; omega

/-- AFP `pass1_len`: `len (pass1 h) ≤ len h`. -/
theorem pass1_len [LinearOrder α] (h : BTree α) : len (pass1 h) ≤ len h := by
  induction h using BTree_ind with
  | step t ih =>
    cases t with
    | leaf => simp [pass1_leaf]
    | node l x r =>
      cases r with
      | leaf => simp [pass1_node_leaf]
      | node m y r' =>
        rw [pass1_cons2]
        have hlt : sizeTree r' < sizeTree (.node l x (.node m y r')) := by
          simp only [sizeTree_node]; omega
        have hIH := ih r' hlt
        calc len (link (.node l x (.node m y (pass1 r'))))
            ≤ len (.node l x (.node m y (pass1 r'))) := len_link _
          _ = 2 + len (pass1 r') := by simp only [len_node]; omega
          _ ≤ 2 + len r' := by omega
          _ = len (.node l x (.node m y r')) := by simp only [len_node]; omega

/-! ### Timing functions: `time_fun` for the Tree variant -/

/-- `T_link` (Tree version): `link` is non-recursive, so its time is 0
(AFP `T_link_0[simp]`). -/
def Tlink : BTree α → ℕ
  | _ => 0

theorem Tlink_eq_zero (t : BTree α) : Tlink t = 0 := rfl

/-- `T_pass1` (Tree version): 1 per equation of the recursive function,
matching Appendix B's `Tpass1` equations (the List2 form). -/
def Tpass1 : BTree α → ℕ
  | .node _ _ (.node _ _ hs) => Tpass1 hs + 1
  | _ => 1

theorem Tpass1_leaf : Tpass1 (BTree.leaf : BTree α) = 1 := by simp [Tpass1]

theorem Tpass1_node_leaf (l : BTree α) (x : α) :
    Tpass1 (.node l x .leaf) = 1 := by simp [Tpass1]

theorem Tpass1_cons2 (hsx hsy hs : BTree α) (x y : α) :
    Tpass1 (.node hsx x (.node hsy y hs)) = Tpass1 hs + 1 := by simp [Tpass1]

/-- `T_pass2` (Tree version): 1 per spine step plus 1 for the base. -/
def Tpass2 : BTree α → ℕ
  | .node _ _ hs => Tpass2 hs + 1
  | .leaf => 1

theorem Tpass2_leaf : Tpass2 (BTree.leaf : BTree α) = 1 := by simp [Tpass2]

theorem Tpass2_cons (hsx hs : BTree α) (x : α) :
    Tpass2 (.node hsx x hs) = Tpass2 hs + 1 := by simp [Tpass2]

/-- `T_del_min` (Tree version): non-recursive, charges only its callees. -/
def TdelMin [LinearOrder α] : BTree α → ℕ
  | .leaf => 0
  | .node hs _ _ => Tpass1 hs + Tpass2 (pass1 hs)

theorem TdelMin_leaf [LinearOrder α] : TdelMin (BTree.leaf : BTree α) = 0 := by
  simp [TdelMin]

theorem TdelMin_node [LinearOrder α] (hs : BTree α) (x : α) (r : BTree α) :
    TdelMin (.node hs x r) = Tpass1 hs + Tpass2 (pass1 hs) := by simp [TdelMin]

/-- `T_merge` (Tree version): `merge` is non-recursive, so its time is 0
(AFP `T_merge_0[simp]`). -/
def Tmerge : BTree α → BTree α → ℕ
  | _, _ => 0

theorem Tmerge_eq_zero (h1 h2 : BTree α) : Tmerge h1 h2 = 0 := rfl

/-- `T_insert` (Tree version): `insert` is non-recursive, so its time is 0. -/
def Tinsert : α → BTree α → ℕ
  | _, _ => 0

theorem Tinsert_eq_zero (x : α) (h : BTree α) : Tinsert x h = 0 := rfl

/-- The time bound the AFP's `A_del_min` proof uses
(`T_pass2 (pass1 hs1) + T_pass1 hs1 ≤ len hs1 + 2`, by `pass1`-induction):
the `pass1` recursion adds 2 to both sides per step, and `pass2` of a
root costs 2. -/
theorem Tpass2_pass1_add_Tpass1 [LinearOrder α] (hs : BTree α) :
    Tpass2 (pass1 hs) + Tpass1 hs ≤ len hs + 2 := by
  induction hs using BTree_ind with
  | step t ih =>
    cases t with
    | leaf =>
      rw [pass1_leaf, Tpass2_leaf, Tpass1_leaf, len_leaf]
    | node l x r =>
      cases r with
      | leaf =>
        rw [pass1_node_leaf, Tpass1_node_leaf, Tpass2_cons, Tpass2_leaf, len_node,
          len_leaf]
      | node m y r' =>
        rw [pass1_cons2, Tpass1_cons2]
        obtain ⟨l', a, hlink⟩ := link_struct (hsx := l) (x := x) (hsy := m) (y := y)
          (hs := pass1 r')
        rw [hlink, Tpass2_cons]
        have hlt : sizeTree r' < sizeTree (.node l x (.node m y r')) := by
          simp only [sizeTree_node]; omega
        have hIH := ih r' hlt
        rw [len_node, len_node]
        omega

/-- AFP `A_insert` (Tree version): the amortized cost of `insert` is at
most `log 2 (size h + 1)`. -/
theorem A_insert [LinearOrder α] (x : α) {h : BTree α} (hr : isRoot h) :
    (Tinsert x h : ℝ) + phiTree (insert x h) - phiTree h
      ≤ Real.logb 2 ((sizeTree h : ℝ) + 1) := by
  rw [Tinsert_eq_zero, Nat.cast_zero, zero_add]
  exact deltaPhi_insert x hr

/-- A log term over a merged size is nonnegative (used for the `leaf`
cases of `A_merge`). -/
theorem logb_nonneg_size_add (a b : BTree α) :
    0 ≤ Real.logb 2 (((sizeTree a + sizeTree b + 1 : ℕ) : ℝ)) :=
  Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by
    have h : (1 : ℕ) ≤ sizeTree a + sizeTree b + 1 := by omega
    exact_mod_cast h)

/-- AFP `A_merge` (Tree version): the amortized cost of `merge` is at
most `log 2 (size h1 + size h2 + 1) + 1`. -/
theorem A_merge [LinearOrder α] {h1 h2 : BTree α} (h1r : isRoot h1)
    (h2r : isRoot h2) :
    (Tmerge h1 h2 : ℝ) + phiTree (merge h1 h2) - phiTree h1 - phiTree h2
      ≤ Real.logb 2 (((sizeTree h1 + sizeTree h2 + 1 : ℕ) : ℝ)) + 1 := by
  rw [Tmerge_eq_zero, Nat.cast_zero, zero_add]
  cases h1 with
  | leaf =>
    rw [merge_leaf_left, phiTree_leaf, sub_zero, sub_self]
    have hnonneg := logb_nonneg_size_add (.leaf : BTree α) h2
    linarith
  | node hs1 x1 r1 =>
    cases h2 with
    | leaf =>
      rw [merge_leaf_right, phiTree_leaf, sub_zero, sub_self]
      have hnonneg := logb_nonneg_size_add (.node hs1 x1 r1) (.leaf : BTree α)
      linarith
    | node hs2 x2 r2 =>
      rw [isRoot_node] at h1r h2r
      subst h1r
      subst h2r
      have hmerge := deltaPhi_merge hs1 hs2 x1 x2 rfl rfl
      have hmono : Real.logb 2 (((sizeTree (.node hs1 x1 .leaf)
              + sizeTree (.node hs2 x2 .leaf) : ℕ) : ℝ))
          ≤ Real.logb 2 (((sizeTree (.node hs1 x1 .leaf)
              + sizeTree (.node hs2 x2 .leaf) + 1 : ℕ) : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (Nat.cast_pos.mpr (by rw [sizeTree_node, sizeTree_leaf]; omega))
        push_cast
        have h0 : (0 : ℝ) ≤ (sizeTree hs1 : ℝ) := by positivity
        have h1 : (0 : ℝ) ≤ (sizeTree hs2 : ℝ) := by positivity
        linarith
      linarith

/-- AFP `A_del_min` (Tree version): the amortized cost of `del_min` is at
most `2·log 2 (size h + 1) + 4`. -/
theorem A_delMin [LinearOrder α] {h : BTree α} (hr : isRoot h) :
    (TdelMin h : ℝ) + phiTree (delMin h) - phiTree h
      ≤ 2 * Real.logb 2 ((sizeTree h : ℝ) + 1) + 4 := by
  cases h with
  | leaf =>
    rw [delMin_leaf, TdelMin_leaf, phiTree_leaf, sizeTree_leaf]
    norm_num [Real.logb_one]
  | node hs x r =>
    rw [isRoot_node] at hr
    subst hr
    rw [delMin_node, TdelMin_node]
    have hT := Tpass2_pass1_add_Tpass1 hs
    have hphi := deltaPhi_delMin hs x
    rw [delMin_node] at hphi
    have hmono : Real.logb 2 ((sizeTree hs : ℝ) + 1)
        ≤ Real.logb 2 ((sizeTree (.node hs x .leaf) : ℝ) + 1) := by
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      rw [sizeTree_node, sizeTree_leaf]
      push_cast
      have h0 : (0 : ℝ) ≤ (sizeTree hs : ℝ) := by positivity
      have h1 : (0 : ℝ) ≤ (sizeTree (.leaf : BTree α) : ℝ) := by positivity
      linarith
    have hcast : ((Tpass1 hs + Tpass2 (pass1 hs) : ℕ) : ℝ)
        = (Tpass1 hs : ℝ) + (Tpass2 (pass1 hs) : ℝ) := by push_cast; ring
    have hT' : (Tpass1 hs : ℝ) + (Tpass2 (pass1 hs) : ℝ) ≤ (len hs : ℝ) + 2 := by
      have hTnat : Tpass1 hs + Tpass2 (pass1 hs) ≤ len hs + 2 := by
        rw [Nat.add_comm]; exact hT
      exact_mod_cast hTnat
    have hlen : (0 : ℝ) ≤ (len hs : ℝ) := by positivity
    rw [hcast]
    linarith [hphi, hT', hmono, hlen]

/-! ### The `Amortized` interpretation for the Tree variant -/

/-- `exec` from `Pairing_Heap_Tree_Analysis2.thy` (same catch-all note as
`execOp`). -/
def execTree [LinearOrder α] : Op α → List (BTree α) → BTree α
  | .Empty, [] => .leaf
  | .DelMin, [h] => delMin h
  | .Insert x, [h] => insert x h
  | .Merge, [h1, h2] => merge h1 h2
  | _, _ => .leaf

theorem execTree_empty [LinearOrder α] :
    execTree (.Empty : Op α) [] = .leaf := rfl

theorem execTree_delMin [LinearOrder α] (h : BTree α) :
    execTree (.DelMin : Op α) [h] = delMin h := rfl

theorem execTree_insert [LinearOrder α] (x : α) (h : BTree α) :
    execTree (.Insert x) [h] = insert x h := rfl

theorem execTree_merge [LinearOrder α] (h1 h2 : BTree α) :
    execTree (.Merge : Op α) [h1, h2] = merge h1 h2 := rfl

/-- `cost` from `Pairing_Heap_Tree_Analysis2.thy`. -/
def costTree [LinearOrder α] : Op α → List (BTree α) → ℕ
  | .Empty, _ => 0
  | .Insert x, [h] => Tinsert x h
  | .DelMin, [h] => TdelMin h
  | .Merge, [h1, h2] => Tmerge h1 h2
  | _, _ => 0

theorem costTree_empty [LinearOrder α] (ss : List (BTree α)) :
    costTree (.Empty : Op α) ss = 0 := rfl

theorem costTree_insert [LinearOrder α] (x : α) (h : BTree α) :
    costTree (.Insert x) [h] = Tinsert x h := rfl

theorem costTree_delMin [LinearOrder α] (h : BTree α) :
    costTree (.DelMin : Op α) [h] = TdelMin h := rfl

theorem costTree_merge [LinearOrder α] (h1 h2 : BTree α) :
    costTree (.Merge : Op α) [h1, h2] = Tmerge h1 h2 := rfl

/-- `U` from `Pairing_Heap_Tree_Analysis2.thy`. -/
noncomputable def UTree [LinearOrder α] : Op α → List (BTree α) → ℝ
  | .Empty, _ => 0
  | .Insert _, [h] => Real.logb 2 ((sizeTree h : ℝ) + 1)
  | .DelMin, [h] => 2 * Real.logb 2 ((sizeTree h : ℝ) + 1) + 4
  | .Merge, [h1, h2] => Real.logb 2 (((sizeTree h1 + sizeTree h2 + 1 : ℕ) : ℝ)) + 1
  | _, _ => 0

theorem UTree_empty [LinearOrder α] (ss : List (BTree α)) :
    UTree (.Empty : Op α) ss = 0 := rfl

theorem UTree_insert [LinearOrder α] (x : α) (h : BTree α) :
    UTree (.Insert x) [h] = Real.logb 2 ((sizeTree h : ℝ) + 1) := rfl

theorem UTree_delMin [LinearOrder α] (h : BTree α) :
    UTree (.DelMin : Op α) [h] = 2 * Real.logb 2 ((sizeTree h : ℝ) + 1) + 4 := rfl

theorem UTree_merge [LinearOrder α] (h1 h2 : BTree α) :
    UTree (.Merge : Op α) [h1, h2] =
      Real.logb 2 (((sizeTree h1 + sizeTree h2 + 1 : ℕ) : ℝ)) + 1 := rfl

/-- The `Amortized` instance for the Tree variant: the AFP's
`interpretation Amortized` with `inv = is_root` as data. -/
noncomputable def pairingTreeAmortized [LinearOrder α] :
    AmortizedData (Op α) (BTree α) where
  arity := arityOp
  exec := execTree
  inv := isRoot
  cost := costTree
  Phi := phiTree
  U := UTree
  inv_exec := by
    intro f ss hinv hlen
    cases f with
    | Empty =>
      cases ss with
      | nil => exact trivial
      | cons _ _ => simp [arityOp] at hlen
    | Insert x =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons h ss =>
        cases ss with
        | nil =>
          have hh : isRoot h := hinv h (by simp)
          change isRoot (insert x h)
          exact isRoot_insert hh
        | cons _ _ => simp [arityOp] at hlen
    | DelMin =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons h ss =>
        cases ss with
        | nil =>
          have hh : isRoot h := hinv h (by simp)
          change isRoot (delMin h)
          exact isRoot_delMin hh
        | cons _ _ => simp [arityOp] at hlen
    | Merge =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons h1 ss =>
        cases ss with
        | nil => simp [arityOp] at hlen
        | cons h2 ss =>
          cases ss with
          | nil =>
            have hh1 : isRoot h1 := hinv h1 (by simp)
            have hh2 : isRoot h2 := hinv h2 (by simp)
            change isRoot (merge h1 h2)
            exact isRoot_merge hh1 hh2
          | cons _ _ => simp [arityOp] at hlen
  ppos := by
    intro s _
    exact phiTree_nonneg s
  U_bound := by
    intro f ss hinv hlen
    cases f with
    | Empty =>
      cases ss with
      | nil => simp [costTree, execTree, UTree, phiTree_leaf]
      | cons _ _ => simp [arityOp] at hlen
    | Insert x =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons h ss =>
        cases ss with
        | nil =>
          have hh : isRoot h := hinv h (by simp)
          rw [show costTree (.Insert x) [h] = Tinsert x h from rfl,
            show execTree (.Insert x) [h] = insert x h from rfl,
            show UTree (.Insert x) [h] =
              Real.logb 2 ((sizeTree h : ℝ) + 1) from rfl,
            show ([h].map phiTree).sum = phiTree h from by simp]
          exact A_insert x hh
        | cons _ _ => simp [arityOp] at hlen
    | DelMin =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons h ss =>
        cases ss with
        | nil =>
          have hh : isRoot h := hinv h (by simp)
          rw [show costTree (.DelMin : Op α) [h] = TdelMin h from rfl,
            show execTree (.DelMin : Op α) [h] = delMin h from rfl,
            show UTree (.DelMin : Op α) [h] =
              2 * Real.logb 2 ((sizeTree h : ℝ) + 1) + 4 from rfl,
            show ([h].map phiTree).sum = phiTree h from by simp]
          exact A_delMin hh
        | cons _ _ => simp [arityOp] at hlen
    | Merge =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons h1 ss =>
        cases ss with
        | nil => simp [arityOp] at hlen
        | cons h2 ss =>
          cases ss with
          | nil =>
            have hh1 : isRoot h1 := hinv h1 (by simp)
            have hh2 : isRoot h2 := hinv h2 (by simp)
            rw [show costTree (.Merge : Op α) [h1, h2] = Tmerge h1 h2 from rfl,
              show execTree (.Merge : Op α) [h1, h2] = merge h1 h2 from rfl,
              show UTree (.Merge : Op α) [h1, h2] =
                Real.logb 2 (((sizeTree h1 + sizeTree h2 + 1 : ℕ) : ℝ)) + 1 from rfl,
              show ([h1, h2].map phiTree).sum = phiTree h1 + phiTree h2 from by simp,
              ← sub_sub]
            exact A_merge hh1 hh2
          | cons _ _ => simp [arityOp] at hlen

/-- The framework's main consequence for the Tree variant: the true cost
of any well-formed operation tree is bounded by the sum of the `U` bounds
(AFP `t_sum_le_U_sum`, instantiated). -/
theorem pairingTree_t_sum_le_U_sum [LinearOrder α] (ot : RoseTree (Op α))
    (hwf : wf pairingTreeAmortized ot) :
    cost_sum pairingTreeAmortized ot ≤ U_sum pairingTreeAmortized ot :=
  t_sum_le_U_sum pairingTreeAmortized hwf

end Tree

namespace List2

/-! ### Size `sz` and potential `Φ` (book §23.2) -/

/- The book's size function. `szList (Hp x hsl :: hsr) = szList hsl + szList hsr + 1`
looks unusual, but it is exactly the total number of constructors in the
list (see `szList_eq_sizeHpList`). -/
mutual
def szHp : Hp α → ℕ
  | .mk _ hs => szList hs + 1
def szList : List (Hp α) → ℕ
  | [] => 0
  | .mk x hsl :: hsr => szList hsl + szList hsr + 1
end

theorem szHp_eq (x : α) (hs : List (Hp α)) :
    szHp (.mk x hs) = szList hs + 1 := rfl

theorem szList_nil : szList ([] : List (Hp α)) = 0 := by simp [szList]

theorem szList_cons (x : α) (hsl hsr : List (Hp α)) :
    szList (.mk x hsl :: hsr) = szList hsl + szList hsr + 1 := by
  simp [szList]

def szHeap : Heap α → ℕ
  | none => 0
  | some h => szHp h

@[simp] theorem szHeap_none : szHeap (none : Heap α) = 0 := rfl

@[simp] theorem szHeap_some (h : Hp α) : szHeap (some h) = szHp h := rfl

theorem szList_eq_sizeHpList (hs : List (Hp α)) :
    szList hs = sizeHpList hs := by
  induction hs using List_size_ind with
  | step hs ih =>
    cases hs with
    | nil => rw [szList_nil, sizeHpList_nil]
    | cons h hs =>
      obtain ⟨x, hsl⟩ := h
      rw [szList_cons, sizeHpList_cons, sizeHp_eq]
      have ih1 := ih hsl
      have ih2 := ih hs
      have hsz1 : sizeHpList hsl < sizeHpList (.mk x hsl :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; omega
      have hsz2 : sizeHpList hs < sizeHpList (.mk x hsl :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; have := sizeHp_pos (.mk x hsl); omega
      rw [ih hsl hsz1, ih hs hsz2]
      omega

theorem szHp_eq_sizeHp (h : Hp α) : szHp h = sizeHp h := by
  obtain ⟨x, hs⟩ := h
  rw [szHp_eq, szList_eq_sizeHpList, sizeHp_eq]
  omega

theorem szHp_pos (h : Hp α) : 0 < szHp h := by
  rw [szHp_eq_sizeHp]; exact sizeHp_pos h

theorem szList_singleton (h : Hp α) : szList [h] = szHp h := by
  obtain ⟨x, hs⟩ := h
  rw [szList_cons, szList_nil, szHp_eq]

/- The book's potential function (overloaded in the book; `lg` is
`Real.logb 2`). -/
mutual
noncomputable def phiHp : Hp α → ℝ
  | .mk _ hs => phiList hs + Real.logb 2 ((szList hs : ℝ) + 1)
noncomputable def phiList : List (Hp α) → ℝ
  | [] => 0
  | .mk _ hsl :: hsr =>
    phiList hsl + phiList hsr + Real.logb 2 ((szList hsl : ℝ) + (szList hsr : ℝ) + 1)
end

theorem phiHp_eq (x : α) (hs : List (Hp α)) :
    phiHp (.mk x hs) = phiList hs + Real.logb 2 ((szList hs : ℝ) + 1) := rfl

theorem phiList_nil : phiList ([] : List (Hp α)) = 0 := by simp [phiList]

theorem phiList_cons (x : α) (hsl hsr : List (Hp α)) :
    phiList (.mk x hsl :: hsr) =
      phiList hsl + phiList hsr +
        Real.logb 2 ((szList hsl : ℝ) + (szList hsr : ℝ) + 1) := by
  simp [phiList]

noncomputable def phiHeap : Heap α → ℝ
  | none => 0
  | some h => phiHp h

@[simp] theorem phiHeap_none : phiHeap (none : Heap α) = 0 := rfl

@[simp] theorem phiHeap_some (h : Hp α) : phiHeap (some h) = phiHp h := rfl

theorem phiList_singleton (h : Hp α) : phiList [h] = phiHp h := by
  obtain ⟨x, hs⟩ := h
  simp [phiList_cons, phiList_nil, phiHp_eq, szList_nil]

theorem phiList_nonneg (hs : List (Hp α)) : 0 ≤ phiList hs := by
  induction hs using List_size_ind with
  | step hs ih =>
    cases hs with
    | nil => rw [phiList_nil]
    | cons h hs =>
      obtain ⟨x, hsl⟩ := h
      rw [phiList_cons]
      have hsz1 : sizeHpList hsl < sizeHpList (.mk x hsl :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; omega
      have hsz2 : sizeHpList hs < sizeHpList (.mk x hsl :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; have := sizeHp_pos (.mk x hsl); omega
      have ih1 := ih hsl hsz1
      have ih2 := ih hs hsz2
      have hlog : 0 ≤ Real.logb 2 ((szList hsl : ℝ) + (szList hs : ℝ) + 1) := by
        apply logb_two_nonneg_of_one_le
        have h1 : (0 : ℝ) ≤ (szList hs : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ (szList hsl : ℝ) := by positivity
        linarith
      linarith

theorem phiHp_nonneg (h : Hp α) : 0 ≤ phiHp h := by
  obtain ⟨x, hs⟩ := h
  rw [phiHp_eq]
  have h1 := phiList_nonneg hs
  have h2 : 0 ≤ Real.logb 2 ((szList hs : ℝ) + 1) := by
    apply logb_two_nonneg_of_one_le
    have : (0 : ℝ) ≤ (szList hs : ℝ) := by positivity
    linarith
  linarith

theorem phiHeap_nonneg (ho : Heap α) : 0 ≤ phiHeap ho := by
  cases ho with
  | none => simp
  | some h => simpa using phiHp_nonneg h

/-- `sz` of the children of a link (AFP `sz_hps_link`). -/
theorem szList_hps_link [LinearOrder α] (h1 h2 : Hp α) :
    szList (hps (link h1 h2)) = szHp h1 + szHp h2 - 1 := by
  obtain ⟨x1, hs1⟩ := h1
  obtain ⟨x2, hs2⟩ := h2
  by_cases hc : x1 < x2
  · rw [link_eq_pos hc]
    change szList (.mk x2 hs2 :: hs1) = _
    rw [szList_cons, szHp_eq, szHp_eq]
    omega
  · rw [link_eq_neg hc]
    change szList (.mk x1 hs1 :: hs2) = _
    rw [szList_cons, szHp_eq, szHp_eq]
    omega

theorem szHp_link [LinearOrder α] (h1 h2 : Hp α) :
    szHp (link h1 h2) = szHp h1 + szHp h2 := by
  obtain ⟨x1, hs1⟩ := h1
  obtain ⟨x2, hs2⟩ := h2
  by_cases hc : x1 < x2
  · rw [link_eq_pos hc, szHp_eq, szList_cons, szHp_eq, szHp_eq]
    omega
  · rw [link_eq_neg hc, szHp_eq, szList_cons, szHp_eq, szHp_eq]
    omega

/-- Potential of a link, i.e. the book's identity (\*) in the proof of
Lemma 23.3. -/
theorem phiHp_link [LinearOrder α] (h1 h2 : Hp α) :
    phiHp (link h1 h2) =
      phiList (hps h1) + phiList (hps h2) +
        Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ) - 1) +
        Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ)) := by
  obtain ⟨x1, hs1⟩ := h1
  obtain ⟨x2, hs2⟩ := h2
  by_cases hc : x1 < x2
  · rw [link_eq_pos hc]
    show phiHp (.mk x1 (.mk x2 hs2 :: hs1)) = _
    rw [phiHp_eq, phiList_cons]
    have hsz : szList (.mk x2 hs2 :: hs1) + 1 = szHp (.mk x1 hs1) + szHp (.mk x2 hs2) := by
      rw [szList_cons, szHp_eq, szHp_eq]; omega
    have hlog2 : Real.logb 2 ((szList (.mk x2 hs2 :: hs1) : ℝ) + 1) =
        Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ)) := by
      congr 1
      have : ((szList (.mk x2 hs2 :: hs1) : ℝ) + 1) =
          ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ)) := by
        have hsz' : szList (.mk x2 hs2 :: hs1) + 1 = szHp (.mk x1 hs1) + szHp (.mk x2 hs2) := hsz
        have := congrArg (fun n : ℕ => (n : ℝ)) hsz'
        push_cast at this
        linarith
      exact this
    have hlog1 : Real.logb 2 ((szList hs2 : ℝ) + (szList hs1 : ℝ) + 1) =
        Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) - 1) := by
      congr 1
      rw [szHp_eq, szHp_eq]
      push_cast
      ring
    rw [hlog2, hlog1]
    ac_rfl
  · rw [link_eq_neg hc]
    show phiHp (.mk x2 (.mk x1 hs1 :: hs2)) = _
    rw [phiHp_eq, phiList_cons]
    have hsz : szList (.mk x1 hs1 :: hs2) + 1 = szHp (.mk x1 hs1) + szHp (.mk x2 hs2) := by
      rw [szList_cons, szHp_eq, szHp_eq]; omega
    have hlog2 : Real.logb 2 ((szList (.mk x1 hs1 :: hs2) : ℝ) + 1) =
        Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ)) := by
      congr 1
      have hsz' : szList (.mk x1 hs1 :: hs2) + 1 = szHp (.mk x1 hs1) + szHp (.mk x2 hs2) := hsz
      have := congrArg (fun n : ℕ => (n : ℝ)) hsz'
      push_cast at this
      linarith
    have hlog1 : Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + 1) =
        Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) - 1) := by
      congr 1
      rw [szHp_eq, szHp_eq]
      push_cast
      ring
    rw [hlog2, hlog1]
    ac_rfl

/-- Potential change of `link` (AFP `ΔΦ_link`). -/
theorem deltaPhi_link [LinearOrder α] (h1 h2 : Hp α) :
    phiHp (link h1 h2) - phiHp h1 - phiHp h2 ≤
      2 * Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ)) := by
  obtain ⟨x1, hs1⟩ := h1
  obtain ⟨x2, hs2⟩ := h2
  have hphi := phiHp_link (.mk x1 hs1) (.mk x2 hs2)
  have hphi1 : phiHp (.mk x1 hs1) = phiList hs1 + Real.logb 2 ((szHp (.mk x1 hs1) : ℝ)) := by
    rw [phiHp_eq]
    congr 1
    rw [szHp_eq]
    push_cast
    ring
  have hphi2 : phiHp (.mk x2 hs2) = phiList hs2 + Real.logb 2 ((szHp (.mk x2 hs2) : ℝ)) := by
    rw [phiHp_eq]
    congr 1
    rw [szHp_eq]
    push_cast
    ring
  have h1p : 0 < szHp (.mk x1 hs1) := szHp_pos _
  have h2p : 0 < szHp (.mk x2 hs2) := szHp_pos _
  have hsum : (0 : ℝ) < (szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) := by positivity
  have h1pr : (1 : ℝ) ≤ (szHp (.mk x1 hs1) : ℝ) := by exact_mod_cast h1p
  have h2pr : (1 : ℝ) ≤ (szHp (.mk x2 hs2) : ℝ) := by exact_mod_cast h2p
  have hlog1 : Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) - 1) ≤
      Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ)) := by
    rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by linarith) hsum]
    linarith
  have hlog2 : 0 ≤ Real.logb 2 ((szHp (.mk x1 hs1) : ℝ)) := by
    apply logb_two_nonneg_of_one_le; exact_mod_cast h1p
  have hlog3 : 0 ≤ Real.logb 2 ((szHp (.mk x2 hs2) : ℝ)) := by
    apply logb_two_nonneg_of_one_le; exact_mod_cast h2p
  rw [show hps (.mk x1 hs1) = hs1 from rfl, show hps (.mk x2 hs2) = hs2 from rfl] at hphi
  rw [hphi, hphi1, hphi2]
  linarith

/-- Potential change of `insert` (AFP `ΔΦ_insert`). -/
theorem deltaPhi_insert [LinearOrder α] (x : α) (ho : Heap α) :
    phiHeap (insert x ho) - phiHeap ho ≤ Real.logb 2 ((szHeap ho : ℝ) + 1) := by
  cases ho with
  | none =>
    change phiHeap (some (.mk x [])) - phiHeap none ≤ Real.logb 2 ((szHeap none : ℝ) + 1)
    rw [phiHeap_none, szHeap_none, phiHeap_some, phiHp_eq, phiList_nil, szList_nil]
    simp
  | some h =>
    obtain ⟨r, hs⟩ := h
    change phiHeap (some (link (.mk x []) (.mk r hs))) - phiHeap (some (.mk r hs)) ≤ _
    rw [phiHeap_some, phiHeap_some, szHeap_some]
    have hlink := phiHp_link (.mk x []) (.mk r hs)
    have hphi : phiHp (.mk r hs) = phiList hs + Real.logb 2 ((szHp (.mk r hs) : ℝ)) := by
      rw [phiHp_eq]
      congr 1
      rw [szHp_eq]
      push_cast
      ring
    have hsz1 : szHp (.mk x []) = 1 := by rw [szHp_eq, szList_nil]
    have hlist : phiList (hps (.mk x [])) = 0 := by
      rw [show hps (.mk x []) = [] from rfl, phiList_nil]
    rw [hlink, hlist, hsz1, hphi, show hps (.mk r hs) = hs from rfl]
    simp only [Nat.cast_one]
    have hpos : (0 : ℝ) < (szHp (.mk r hs) : ℝ) := by
      have := szHp_pos (.mk r hs); exact_mod_cast this
    have hlog : Real.logb 2 ((1 : ℝ) + (szHp (.mk r hs) : ℝ) - 1) =
        Real.logb 2 ((szHp (.mk r hs) : ℝ)) := by
      congr 1; ring
    rw [hlog]
    have hlog2 : Real.logb 2 ((1 : ℝ) + (szHp (.mk r hs) : ℝ)) =
        Real.logb 2 ((szHp (.mk r hs) : ℝ) + 1) := by
      congr 1; ring
    rw [hlog2]
    linarith

/-! ### `pass1` / `pass2`: size lemmas -/

theorem szList_pass1 [LinearOrder α] (hs : List (Hp α)) :
    szList (pass1 hs) = szList hs := by
  induction hs using List_pair_ind with
  | nil => rfl
  | single h => rfl
  | cons2 h1 h2 hs ih =>
    obtain ⟨x1, hs1⟩ := h1
    obtain ⟨x2, hs2⟩ := h2
    by_cases hc : x1 < x2
    · rw [pass1_cons2, link_eq_pos hc, szList_cons, szList_cons, ih, szList_cons,
        szList_cons]
      omega
    · rw [pass1_cons2, link_eq_neg hc, szList_cons, szList_cons, ih, szList_cons,
        szList_cons]
      omega

/-- `phiList` of the children of a link (the part of the book's identity (\*)
that survives after cancelling the `Φ(link)` potential against its own
children's potential). -/
theorem phiList_hps_link [LinearOrder α] (h1 h2 : Hp α) :
    phiList (hps (link h1 h2)) =
      phiList (hps h1) + phiList (hps h2) +
        Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ) - 1) := by
  have hphi := phiHp_link h1 h2
  have hphi2 : phiHp (link h1 h2) =
      phiList (hps (link h1 h2)) +
        Real.logb 2 ((szList (hps (link h1 h2)) : ℝ) + 1) := by
    cases hlk : link h1 h2 with
    | mk x hs => rfl
  have hsz : szList (hps (link h1 h2)) + 1 = szHp h1 + szHp h2 := by
    have h := szList_hps_link h1 h2
    have h1p : 0 < szHp h1 := szHp_pos h1
    have h2p : 0 < szHp h2 := szHp_pos h2
    omega
  have hlog : Real.logb 2 ((szList (hps (link h1 h2)) : ℝ) + 1) =
      Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ)) := by
    congr 1
    have := congrArg (fun n : ℕ => (n : ℝ)) hsz
    push_cast at this
    linarith
  rw [hphi2, hlog] at hphi
  linarith

theorem szList_pass2 [LinearOrder α] (hs : List (Hp α)) :
    szHeap (pass2 hs) = szList hs := by
  induction hs with
  | nil => rw [pass2_nil, szHeap_none, szList_nil]
  | cons h hs ih =>
    rw [pass2_cons]
    cases hpass : pass2 hs with
    | none =>
      have hhs : hs = [] := by
        rw [← pass2_eq_none_iff]; exact hpass
      subst hhs
      simp [szList_singleton]
    | some h' =>
      have hih : szHp h' = szList hs := by
        have := ih
        rw [hpass] at this
        simpa using this
      simp only [szHeap_some, szHp_link, hih]
      obtain ⟨x, hsl⟩ := h
      rw [szList_cons, szHp_eq]
      omega

/-! ### Lemma 23.2 (`ΔΦ_pass1`) -/

theorem deltaPhi_pass1 [LinearOrder α] (hs : List (Hp α)) :
    phiList (pass1 hs) - phiList hs ≤
      2 * Real.logb 2 ((szList hs : ℝ) + 1) - (hs.length : ℝ) + 2 := by
  induction hs using List_pair_ind with
  | nil =>
    rw [pass1_nil, phiList_nil, szList_nil]
    simp
  | single h =>
    rw [pass1_single]
    have hpos : (0 : ℝ) ≤ Real.logb 2 ((szList [h] : ℝ) + 1) := by
      apply logb_two_nonneg_of_one_le
      have : (1 : ℕ) ≤ szList [h] := by
        rw [szList_singleton]; exact szHp_pos h
      have : (1 : ℝ) ≤ (szList [h] : ℝ) := by exact_mod_cast this
      linarith
    simp
    linarith
  | cons2 h1 h2 hs ih =>
    obtain ⟨x1, hs1⟩ := h1
    obtain ⟨x2, hs2⟩ := h2
    -- Equation for the potential difference, following the book's proof.
    have hDelta : phiList (pass1 (.mk x1 hs1 :: .mk x2 hs2 :: hs)) -
        phiList (.mk x1 hs1 :: .mk x2 hs2 :: hs) =
        Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + 1) -
          Real.logb 2 ((szList hs2 : ℝ) + (szList hs : ℝ) + 1) +
          (phiList (pass1 hs) - phiList hs) := by
      rw [pass1_cons2]
      by_cases hc : x1 < x2
      · rw [link_eq_pos hc]
        have hphi1 : phiList (.mk x1 (.mk x2 hs2 :: hs1) :: pass1 hs) =
            phiList (.mk x2 hs2 :: hs1) + phiList (pass1 hs) +
              Real.logb 2 ((szList (.mk x2 hs2 :: hs1) : ℝ) + (szList (pass1 hs) : ℝ) + 1) := by
          rw [phiList_cons]
        have hphi2 : phiList (.mk x1 hs1 :: .mk x2 hs2 :: hs) =
            phiList hs1 + phiList (.mk x2 hs2 :: hs) +
              Real.logb 2 ((szList hs1 : ℝ) + (szList (.mk x2 hs2 :: hs) : ℝ) + 1) := by
          rw [phiList_cons]
        have hphi3 : phiList (.mk x2 hs2 :: hs) =
            phiList hs2 + phiList hs +
              Real.logb 2 ((szList hs2 : ℝ) + (szList hs : ℝ) + 1) := by
          rw [phiList_cons]
        have hlink : phiList (.mk x2 hs2 :: hs1) =
            phiList hs2 + phiList hs1 +
              Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + 1) := by
          rw [phiList_cons, add_comm (szList hs2 : ℝ) (szList hs1 : ℝ)]
        have hszpass : szList (pass1 hs) = szList hs := szList_pass1 hs
        have hszlink : szList (.mk x2 hs2 :: hs1) = szList hs1 + szList hs2 + 1 := by
          rw [szList_cons]
          omega
        rw [hphi1, hphi2, hphi3, hlink, hszpass]
        have hlog1 : Real.logb 2 ((szList (.mk x2 hs2 :: hs1) : ℝ) + (szList hs : ℝ) + 1) =
            Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) := by
          congr 1
          rw [hszlink]
          push_cast
          ring
        have hlog2 : Real.logb 2 ((szList hs1 : ℝ) + (szList (.mk x2 hs2 :: hs) : ℝ) + 1) =
            Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) := by
          congr 1
          rw [szList_cons]
          push_cast
          ring
        rw [hlog1, hlog2]
        ring
      · rw [link_eq_neg hc]
        have hphi1 : phiList (.mk x2 (.mk x1 hs1 :: hs2) :: pass1 hs) =
            phiList (.mk x1 hs1 :: hs2) + phiList (pass1 hs) +
              Real.logb 2 ((szList (.mk x1 hs1 :: hs2) : ℝ) + (szList (pass1 hs) : ℝ) + 1) := by
          rw [phiList_cons]
        have hphi2 : phiList (.mk x1 hs1 :: .mk x2 hs2 :: hs) =
            phiList hs1 + phiList (.mk x2 hs2 :: hs) +
              Real.logb 2 ((szList hs1 : ℝ) + (szList (.mk x2 hs2 :: hs) : ℝ) + 1) := by
          rw [phiList_cons]
        have hphi3 : phiList (.mk x2 hs2 :: hs) =
            phiList hs2 + phiList hs +
              Real.logb 2 ((szList hs2 : ℝ) + (szList hs : ℝ) + 1) := by
          rw [phiList_cons]
        have hlink : phiList (.mk x1 hs1 :: hs2) =
            phiList hs1 + phiList hs2 +
              Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + 1) := by
          rw [phiList_cons]
        have hszpass : szList (pass1 hs) = szList hs := szList_pass1 hs
        have hszlink : szList (.mk x1 hs1 :: hs2) = szList hs1 + szList hs2 + 1 := by
          rw [szList_cons]
        rw [hphi1, hphi2, hphi3, hlink, hszpass]
        have hlog1 : Real.logb 2 ((szList (.mk x1 hs1 :: hs2) : ℝ) + (szList hs : ℝ) + 1) =
            Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) := by
          congr 1
          rw [hszlink]
          push_cast
          ring
        have hlog2 : Real.logb 2 ((szList hs1 : ℝ) + (szList (.mk x2 hs2 :: hs) : ℝ) + 1) =
            Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) := by
          congr 1
          rw [szList_cons]
          push_cast
          ring
        rw [hlog1, hlog2]
        ring
    -- Now combine with the induction hypothesis and the log inequality.
    have hx : (0 : ℝ) < (szList hs1 : ℝ) + (szList hs2 : ℝ) + 1 := by positivity
    have hy : (0 : ℝ) < (szList hs : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (szList hs : ℝ) := by positivity
      linarith
    have hlogineq0 := ld_sum_inequality hx hy
    have hlogarg : Real.logb 2 (((szList hs1 : ℝ) + (szList hs2 : ℝ) + 1) +
        ((szList hs : ℝ) + 1)) =
        Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) := by
      congr 1
      ring
    rw [hlogarg] at hlogineq0
    have hlogineq : Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + 1) +
        Real.logb 2 ((szList hs : ℝ) + 1) + 2 ≤
        2 * Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) :=
      hlogineq0
    have hlogmono : Real.logb 2 ((szList hs : ℝ) + 1) ≤
        Real.logb 2 ((szList hs2 : ℝ) + (szList hs : ℝ) + 1) := by
      rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
        (by positivity)]
      have : (0 : ℝ) ≤ (szList hs2 : ℝ) := by positivity
      linarith
    have hsz0 : (szList (.mk x1 hs1 :: .mk x2 hs2 :: hs) : ℝ) + 1 =
        (szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 3 := by
      rw [szList_cons, szList_cons]
      push_cast
      ring
    have hlen : ((.mk x1 hs1 :: .mk x2 hs2 :: hs).length : ℝ) = (hs.length : ℝ) + 2 := by
      rw [List.length_cons, List.length_cons]
      push_cast
      ring
    have hlogmono2 : Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 2) ≤
        Real.logb 2 ((szList hs1 : ℝ) + (szList hs2 : ℝ) + (szList hs : ℝ) + 3) := by
      rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)]
      linarith
    rw [hsz0, hlen]
    linarith [hDelta, ih, hlogineq, hlogmono, hlogmono2]

/-! ### Lemma 23.3 (`ΔΦ_pass2`), Corollary 23.4, Theorem 23.1 -/

theorem szList_pos_of_ne_nil [LinearOrder α] {hs : List (Hp α)}
    (hne : hs ≠ []) : 0 < szList hs := by
  cases hs with
  | nil => exact absurd rfl hne
  | cons h hs =>
    obtain ⟨x, hsl⟩ := h
    rw [szList_cons]
    omega

theorem deltaPhi_pass2 [LinearOrder α] {hs : List (Hp α)} (hne : hs ≠ []) :
    phiHeap (pass2 hs) - phiList hs ≤ Real.logb 2 (szList hs : ℝ) := by
  induction hs with
  | nil => exact absurd rfl hne
  | cons h1 hs ih =>
    obtain ⟨x1, hs1⟩ := h1
    by_cases hhs : hs = []
    · subst hhs
      rw [show pass2 [.mk x1 hs1] = some (.mk x1 hs1) from rfl, phiHeap_some,
        phiList_singleton]
      have hlog : 0 ≤ Real.logb 2 (szList [.mk x1 hs1] : ℝ) := by
        apply logb_two_nonneg_of_one_le
        have h1 : (1 : ℕ) ≤ szList [.mk x1 hs1] := by
          rw [szList_singleton]; exact szHp_pos _
        exact_mod_cast h1
      linarith
    · have ih' := ih hhs
      obtain ⟨h2, hpass⟩ := pass2_some_exists hhs
      obtain ⟨x2, hs2⟩ := h2
      have hpass2 : pass2 (.mk x1 hs1 :: hs) =
          some (link (.mk x1 hs1) (.mk x2 hs2)) := by
        rw [pass2_cons, hpass]
      have hsz : szList hs = szHp (.mk x2 hs2) := by
        have h1 := szList_pass2 hs
        rw [hpass] at h1
        simpa using h1.symm
      have hstar : phiList hs2 - phiList hs ≤ 0 := by
        have hphi2 : phiHp (.mk x2 hs2) =
            phiList hs2 + Real.logb 2 ((szList hs2 : ℝ) + 1) := phiHp_eq _ _
        have hih : phiHp (.mk x2 hs2) - phiList hs ≤ Real.logb 2 (szList hs : ℝ) := by
          have := ih'
          rw [hpass] at this
          simpa using this
        have hlogeq : Real.logb 2 ((szList hs2 : ℝ) + 1) =
            Real.logb 2 (szList hs : ℝ) := by
          congr 1
          have hsz2 : szList hs = szList hs2 + 1 := by rw [hsz, szHp_eq]
          rw [hsz2]
          push_cast
          ring
        linarith
      have hDelta : phiHeap (pass2 (.mk x1 hs1 :: hs)) -
          phiList (.mk x1 hs1 :: hs) =
          (phiList hs2 - phiList hs) +
            Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) - 1) := by
        rw [hpass2, phiHeap_some, phiHp_link,
          show hps (.mk x1 hs1) = hs1 from rfl, show hps (.mk x2 hs2) = hs2 from rfl,
          phiList_cons]
        have hlogeq : Real.logb 2 ((szList hs1 : ℝ) + (szList hs : ℝ) + 1) =
            Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ)) := by
          congr 1
          rw [hsz, szHp_eq, szHp_eq]
          push_cast
          ring
        rw [hlogeq]
        ring
      have hlogmono : Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) - 1) ≤
          Real.logb 2 ((szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ)) := by
        have hs1p : (1 : ℝ) ≤ (szHp (.mk x1 hs1) : ℝ) := by
          have := szHp_pos (.mk x1 hs1); exact_mod_cast this
        have hs2p : (1 : ℝ) ≤ (szHp (.mk x2 hs2) : ℝ) := by
          have := szHp_pos (.mk x2 hs2); exact_mod_cast this
        rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by linarith) (by linarith)]
        linarith
      have hszcons : (szList (.mk x1 hs1 :: hs) : ℝ) =
          (szHp (.mk x1 hs1) : ℝ) + (szHp (.mk x2 hs2) : ℝ) := by
        rw [szList_cons, hsz, szHp_eq, szHp_eq]
        push_cast
        ring
      rw [hDelta, hszcons]
      linarith [hstar, hlogmono]

/-- Corollary 23.4 (`ΔΦ_pass2'`). -/
theorem deltaPhi_pass2' [LinearOrder α] (hs : List (Hp α)) :
    phiHeap (pass2 hs) - phiList hs ≤ Real.logb 2 ((szList hs : ℝ) + 1) := by
  by_cases hne : hs = []
  · subst hne
    rw [pass2_nil, phiHeap_none, phiList_nil]
    simp [szList_nil]
  · have h := deltaPhi_pass2 hne
    have hpos : (0 : ℝ) < (szList hs : ℝ) := by
      have := szList_pos_of_ne_nil hne; exact_mod_cast this
    have hmono : Real.logb 2 (szList hs : ℝ) ≤ Real.logb 2 ((szList hs : ℝ) + 1) := by
      rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos (by positivity)]
      have : (0 : ℝ) ≤ (szList hs : ℝ) := by positivity
      linarith
    linarith

/-- Theorem 23.1 (`ΔΦ_delMin`): the main potential bound for `delMin`. -/
theorem deltaPhi_delMin [LinearOrder α] (h : Hp α) :
    phiHeap (delMin (some h)) - phiHeap (some h) ≤
      2 * Real.logb 2 ((szList (hps h) : ℝ) + 1) - ((hps h).length : ℝ) + 2 := by
  obtain ⟨x, hs⟩ := h
  change phiHeap (delMin (some (.mk x hs))) - phiHeap (some (.mk x hs)) ≤
      2 * Real.logb 2 ((szList hs : ℝ) + 1) - (hs.length : ℝ) + 2
  rw [delMin_some, phiHeap_some]
  have hphi : phiHp (.mk x hs) = phiList hs +
      Real.logb 2 ((szList hs : ℝ) + 1) := phiHp_eq _ _
  have h2 : phiHeap (pass2 (pass1 hs)) - phiList (pass1 hs) ≤
      Real.logb 2 ((szList (pass1 hs) : ℝ) + 1) := deltaPhi_pass2' (pass1 hs)
  rw [szList_pass1] at h2
  have h1 := deltaPhi_pass1 hs
  rw [hphi]
  linarith

/-! ### The three amortized bounds -/

theorem A_insert [LinearOrder α] (x : α) (ho : Heap α) :
    (Tinsert x ho : ℝ) + phiHeap (insert x ho) - phiHeap ho ≤
      Real.logb 2 ((szHeap ho : ℝ) + 1) := by
  have hTnat : Tinsert x ho = 0 := rfl
  have hT : (Tinsert x ho : ℝ) = 0 := by rw [hTnat]; simp
  rw [hT, zero_add]
  exact deltaPhi_insert x ho

theorem A_merge [LinearOrder α] (ho1 ho2 : Heap α) :
    (Tmerge ho1 ho2 : ℝ) + phiHeap (merge ho1 ho2) - phiHeap ho1 - phiHeap ho2 ≤
      2 * Real.logb 2 ((szHeap ho1 : ℝ) + (szHeap ho2 : ℝ) + 1) := by
  have hTnat : Tmerge ho1 ho2 = 0 := rfl
  have hT : (Tmerge ho1 ho2 : ℝ) = 0 := by rw [hTnat]; simp
  rw [hT, zero_add]
  cases ho1 with
  | none =>
    rw [merge_none_left, szHeap_none, phiHeap_none]
    simp only [Nat.cast_zero]
    have hlog : 0 ≤ Real.logb 2 ((0 : ℝ) + (szHeap ho2 : ℝ) + 1) := by
      apply logb_two_nonneg_of_one_le
      have : (0 : ℝ) ≤ (szHeap ho2 : ℝ) := by positivity
      linarith
    have hphi := phiHeap_nonneg ho2
    linarith
  | some h1 =>
    cases ho2 with
    | none =>
      rw [merge_none_right, szHeap_none, phiHeap_none]
      simp only [Nat.cast_zero]
      have hlog : 0 ≤ Real.logb 2 ((szHeap (some h1) : ℝ) + (0 : ℝ) + 1) := by
        apply logb_two_nonneg_of_one_le
        have : (0 : ℝ) ≤ (szHeap (some h1) : ℝ) := by positivity
        linarith
      have hphi := phiHeap_nonneg (some h1)
      linarith
    | some h2 =>
      rw [merge_some_some, phiHeap_some, phiHeap_some, phiHeap_some, szHeap_some, szHeap_some]
      have hlink := deltaPhi_link h1 h2
      have hs1p : (1 : ℝ) ≤ (szHp h1 : ℝ) := by
        have := szHp_pos h1; exact_mod_cast this
      have hs2p : (1 : ℝ) ≤ (szHp h2 : ℝ) := by
        have := szHp_pos h2; exact_mod_cast this
      have hmono : Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ)) ≤
          Real.logb 2 ((szHp h1 : ℝ) + (szHp h2 : ℝ) + 1) := by
        rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by linarith) (by linarith)]
        linarith
      linarith

theorem A_delMin [LinearOrder α] (ho : Heap α) :
    (TdelMin ho : ℝ) + phiHeap (delMin ho) - phiHeap ho ≤
      2 * Real.logb 2 ((szHeap ho : ℝ) + 1) + 4 := by
  cases ho with
  | none =>
    simp [TdelMin, delMin, phiHeap_none, szHeap_none, Real.logb_one]
  | some h =>
    obtain ⟨x, hs⟩ := h
    have hTnat : TdelMin (some (.mk x hs)) = hs.length + 2 := by
      change Tpass1 hs + Tpass2 (pass1 hs) = hs.length + 2
      have := Tpass2_pass1_add_Tpass1 hs
      omega
    have hT : (TdelMin (some (.mk x hs)) : ℝ) = (hs.length : ℝ) + 2 := by
      exact_mod_cast hTnat
    have hphi := deltaPhi_delMin (.mk x hs)
    rw [show hps (.mk x hs) = hs from rfl] at hphi
    have hsz : szHeap (some (.mk x hs)) = szList hs + 1 := by
      rw [szHeap_some, szHp_eq]
    have hmono : Real.logb 2 ((szList hs : ℝ) + 1) ≤ Real.logb 2 ((szList hs : ℝ) + 1 + 1) := by
      rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)]
      linarith
    rw [hT]
    rw [show szHeap (some (.mk x hs)) = szList hs + 1 from hsz]
    push_cast
    linarith [hphi, hmono]

/-! ### The `Amortized` interpretation (book §23.2, AFP
`interpretation pairing: Amortized`) -/

/-- `exec` from `Pairing_Heap_List2_Analysis.thy`. Only argument shapes
with `length ss = arityOp f` occur in the locale obligations below;
the catch-all returns `none`. -/
def execOp [LinearOrder α] : Op α → List (Heap α) → Heap α
  | .Empty, [] => none
  | .Insert x, [ho] => insert x ho
  | .DelMin, [ho] => delMin ho
  | .Merge, [ho1, ho2] => merge ho1 ho2
  | _, _ => none

/-- `cost` from `Pairing_Heap_List2_Analysis.thy` (same catch-all note). -/
def costOp [LinearOrder α] : Op α → List (Heap α) → ℕ
  | .Empty, _ => 0
  | .Insert x, [ho] => Tinsert x ho
  | .DelMin, [ho] => TdelMin ho
  | .Merge, [ho1, ho2] => Tmerge ho1 ho2
  | _, _ => 0

/-- The AFP's defining equations for `exec`, `cost`, `U` hold verbatim in
the Lean definitions (the catch-all values never occur in the locale
obligations, which quantify only over argument shapes with
`length ss = arityOp f`). -/
theorem execOp_empty [LinearOrder α] : execOp (.Empty : Op α) [] = none := rfl

theorem execOp_insert [LinearOrder α] (x : α) (ho : Heap α) :
    execOp (.Insert x) [ho] = insert x ho := rfl

theorem execOp_delMin [LinearOrder α] (ho : Heap α) :
    execOp (.DelMin : Op α) [ho] = delMin ho := rfl

theorem execOp_merge [LinearOrder α] (ho1 ho2 : Heap α) :
    execOp (.Merge : Op α) [ho1, ho2] = merge ho1 ho2 := rfl

theorem costOp_empty [LinearOrder α] (ss : List (Heap α)) :
    costOp (.Empty : Op α) ss = 0 := rfl

theorem costOp_insert [LinearOrder α] (x : α) (ho : Heap α) :
    costOp (.Insert x) [ho] = Tinsert x ho := rfl

theorem costOp_delMin [LinearOrder α] (ho : Heap α) :
    costOp (.DelMin : Op α) [ho] = TdelMin ho := rfl

theorem costOp_merge [LinearOrder α] (ho1 ho2 : Heap α) :
    costOp (.Merge : Op α) [ho1, ho2] = Tmerge ho1 ho2 := rfl

/-- `U` from `Pairing_Heap_List2_Analysis.thy` (same catch-all note). -/
noncomputable def UOp [LinearOrder α] : Op α → List (Heap α) → ℝ
  | .Empty, _ => 0
  | .Insert _, [ho] => Real.logb 2 ((szHeap ho : ℝ) + 1)
  | .DelMin, [ho] => 2 * Real.logb 2 ((szHeap ho : ℝ) + 1) + 4
  | .Merge, [ho1, ho2] =>
    2 * Real.logb 2 ((szHeap ho1 : ℝ) + (szHeap ho2 : ℝ) + 1)
  | _, _ => 0

theorem UOp_empty [LinearOrder α] (ss : List (Heap α)) :
    UOp (.Empty : Op α) ss = 0 := rfl

theorem UOp_insert [LinearOrder α] (x : α) (ho : Heap α) :
    UOp (.Insert x) [ho] = Real.logb 2 ((szHeap ho : ℝ) + 1) := rfl

theorem UOp_delMin [LinearOrder α] (ho : Heap α) :
    UOp (.DelMin : Op α) [ho] = 2 * Real.logb 2 ((szHeap ho : ℝ) + 1) + 4 := rfl

theorem UOp_merge [LinearOrder α] (ho1 ho2 : Heap α) :
    UOp (.Merge : Op α) [ho1, ho2] =
      2 * Real.logb 2 ((szHeap ho1 : ℝ) + (szHeap ho2 : ℝ) + 1) := rfl

/-- The three `Amortized` locale obligations for pairing heaps, with
`inv = fun _ => True` as in the AFP interpretation: `inv_exec` is trivial
(since every heap satisfies `True`), `ppos` is `phiHeap_nonneg`, and the
`U` bound is exactly `A_insert` / `A_delMin` / `A_merge` per operation.
The framework's generic consequences (`t_sum_le_U_sum`, …) in
`Amortized_Framework.thy` apply to any `Amortized` instance and are not
re-proved here. -/
theorem amortized [LinearOrder α] :
    (∀ (f : Op α) (ss : List (Heap α)),
      (∀ s ∈ ss, True) → ss.length = arityOp f → True) ∧
    (∀ s : Heap α, True → 0 ≤ phiHeap s) ∧
    (∀ (f : Op α) (ss : List (Heap α)),
      (∀ s ∈ ss, True) → ss.length = arityOp f →
      (costOp f ss : ℝ) + phiHeap (execOp f ss) -
        (ss.map phiHeap).sum ≤ UOp f ss) := by
  refine ⟨by intro _ _ _ _; trivial, fun s _ => phiHeap_nonneg s, ?_⟩
  intro f ss _ hlen
  cases f with
  | Empty =>
    cases ss with
    | nil => simp [costOp, execOp, UOp]
    | cons _ _ => simp [arityOp] at hlen
  | Insert x =>
    cases ss with
    | nil => simp [arityOp] at hlen
    | cons ho ss =>
      cases ss with
      | nil =>
        rw [show costOp (.Insert x) [ho] = Tinsert x ho from rfl,
          show execOp (.Insert x) [ho] = insert x ho from rfl,
          show UOp (.Insert x) [ho] =
            Real.logb 2 ((szHeap ho : ℝ) + 1) from rfl,
          show ([ho].map phiHeap).sum = phiHeap ho from by simp]
        exact A_insert x ho
      | cons _ _ => simp [arityOp] at hlen
  | DelMin =>
    cases ss with
    | nil => simp [arityOp] at hlen
    | cons ho ss =>
      cases ss with
      | nil =>
        rw [show costOp (.DelMin) [ho] = TdelMin ho from rfl,
          show execOp (.DelMin) [ho] = delMin ho from rfl,
          show UOp (.DelMin) [ho] =
            2 * Real.logb 2 ((szHeap ho : ℝ) + 1) + 4 from rfl,
          show ([ho].map phiHeap).sum = phiHeap ho from by simp]
        exact A_delMin ho
      | cons _ _ => simp [arityOp] at hlen
  | Merge =>
    cases ss with
    | nil => simp [arityOp] at hlen
    | cons ho1 ss =>
      cases ss with
      | nil => simp [arityOp] at hlen
      | cons ho2 ss =>
        cases ss with
        | nil =>
          rw [show costOp (.Merge) [ho1, ho2] = Tmerge ho1 ho2 from rfl,
            show execOp (.Merge) [ho1, ho2] = merge ho1 ho2 from rfl,
            show UOp (.Merge) [ho1, ho2] =
              2 * Real.logb 2 ((szHeap ho1 : ℝ) + (szHeap ho2 : ℝ) + 1) from rfl,
            show ([ho1, ho2].map phiHeap).sum =
              phiHeap ho1 + phiHeap ho2 from by simp]
          have h := A_merge ho1 ho2
          have hT : (Tmerge ho1 ho2 : ℝ) = 0 := by
            rw [show Tmerge ho1 ho2 = 0 from rfl]; simp
          rw [hT, zero_add]
          linarith [h]
        | cons _ _ => simp [arityOp] at hlen

/-- The `Amortized` instance for pairing heaps: the AFP's
`interpretation pairing: Amortized` as data. -/
noncomputable def pairingAmortized [LinearOrder α] :
    AmortizedData (Op α) (Heap α) where
  arity := arityOp
  exec := execOp
  inv := fun _ => True
  cost := costOp
  Phi := phiHeap
  U := UOp
  inv_exec := by intro _ _ _ _; trivial
  ppos := by intro s _; exact phiHeap_nonneg s
  U_bound := by
    intro f ss h1 hlen
    exact amortized.2.2 f ss (fun s hs => h1 s hs) hlen

/-- The framework's main consequence for pairing heaps: the true cost of
any well-formed operation tree is bounded by the sum of the `U` bounds
(AFP `t_sum_le_U_sum`, instantiated). -/
theorem pairing_t_sum_le_U_sum [LinearOrder α] (ot : RoseTree (Op α))
    (hwf : wf pairingAmortized ot) :
    cost_sum pairingAmortized ot ≤ U_sum pairingAmortized ot :=
  t_sum_le_U_sum pairingAmortized hwf

/-! ### §23.3 Pairing heaps as trees -/

/- The book's `trees` mapping (§23.3): a heap `Hp x hs` is represented by
`node (trees hs) x leaf`, and a list of heaps by `trees`. -/
mutual
def trees : List (Hp α) → Tree.BTree α
  | [] => .leaf
  | .mk x lhs :: rhs => .node (trees lhs) x (trees rhs)
def treeHp : Hp α → Tree.BTree α
  | .mk x hs => .node (trees hs) x .leaf
end

theorem trees_nil : trees ([] : List (Hp α)) = Tree.BTree.leaf := by
  simp [trees]

theorem trees_cons (x : α) (lhs rhs : List (Hp α)) :
    trees (.mk x lhs :: rhs) = Tree.BTree.node (trees lhs) x (trees rhs) := by
  simp [trees]

/-- Book §23.3, claim 11: `sz hs = |trees hs|` (with `|·|` the tree size). -/
theorem sizeTree_trees (hs : List (Hp α)) :
    Tree.sizeTree (trees hs) = szList hs := by
  induction hs using List_size_ind with
  | step hs ih =>
    cases hs with
    | nil => rw [trees_nil, Tree.sizeTree_leaf, szList_nil]
    | cons h hs =>
      obtain ⟨x, lhs⟩ := h
      have hsz1 : sizeHpList lhs < sizeHpList (.mk x lhs :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; omega
      have hsz2 : sizeHpList hs < sizeHpList (.mk x lhs :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; have := sizeHp_pos (.mk x lhs); omega
      rw [trees_cons, Tree.sizeTree_node, ih lhs hsz1, ih hs hsz2, szList_cons]

/-- Book §23.3, claim 12 (for lists): the list potential is the tree
potential of the `trees` image. -/
theorem phiTree_trees (hs : List (Hp α)) :
    Tree.phiTree (trees hs) = phiList hs := by
  induction hs using List_size_ind with
  | step hs ih =>
    cases hs with
    | nil => rw [trees_nil, Tree.phiTree_leaf, phiList_nil]
    | cons h hs =>
      obtain ⟨x, lhs⟩ := h
      have hsz1 : sizeHpList lhs < sizeHpList (.mk x lhs :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; omega
      have hsz2 : sizeHpList hs < sizeHpList (.mk x lhs :: hs) := by
        rw [sizeHpList_cons, sizeHp_eq]; have := sizeHp_pos (.mk x lhs); omega
      have hsize : Tree.sizeTree (Tree.BTree.node (trees lhs) x (trees hs)) =
          szList lhs + szList hs + 1 := by
        rw [Tree.sizeTree_node, sizeTree_trees, sizeTree_trees]
      rw [trees_cons, Tree.phiTree_node, ih lhs hsz1, ih hs hsz2, phiList_cons]
      have hlog : Real.logb 2 ((Tree.sizeTree (Tree.BTree.node (trees lhs) x (trees hs)) : ℝ)) =
          Real.logb 2 ((szList lhs : ℝ) + (szList hs : ℝ) + 1) := by
        congr 1
        rw [hsize]
        push_cast
        ring
      rw [hlog]
      ac_rfl

/-- Book §23.3: `sz` on a single heap is the size of its tree. -/
theorem szHp_tree (h : Hp α) : szHp h = Tree.sizeTree (treeHp h) := by
  obtain ⟨x, hs⟩ := h
  change szHp (.mk x hs) = Tree.sizeTree (Tree.BTree.node (trees hs) x Tree.BTree.leaf)
  rw [Tree.sizeTree_node, Tree.sizeTree_leaf, sizeTree_trees, szHp_eq]

/-- Book §23.3: `Φ` on a single heap is the potential of its tree. -/
theorem phiHp_tree (h : Hp α) : phiHp h = Tree.phiTree (treeHp h) := by
  obtain ⟨x, hs⟩ := h
  change phiHp (.mk x hs) = Tree.phiTree (Tree.BTree.node (trees hs) x Tree.BTree.leaf)
  rw [Tree.phiTree_node, Tree.phiTree_leaf, phiTree_trees, phiHp_eq]
  have hsize : Tree.sizeTree (Tree.BTree.node (trees hs) x Tree.BTree.leaf) = szList hs + 1 := by
    rw [Tree.sizeTree_node, Tree.sizeTree_leaf, sizeTree_trees]
  have hlog : Real.logb 2 ((Tree.sizeTree (Tree.BTree.node (trees hs) x Tree.BTree.leaf) : ℝ)) =
      Real.logb 2 ((szList hs : ℝ) + 1) := by
    congr 1
    rw [hsize]
    push_cast
    ring
  rw [hlog]
  ring

/-! ### AFP completeness: remaining lemmas of `Pairing_Heap_List2` /
`Pairing_Heap_List2_Analysis` -/

/-- AFP `sz_hps_Cons`: `sz (h # hs) = sz h + sz hs` for a single head heap,
not decomposed into `Hp x hsl`. -/
theorem szList_cons_hp (h : Hp α) (hs : List (Hp α)) :
    szList (h :: hs) = szHp h + szList hs := by
  obtain ⟨x, hsl⟩ := h
  rw [szList_cons, szHp_eq]
  omega

/-- AFP's (commented-out, unused) `Φ_Cons`: `Φ (h # hs) =
Φ (hps h) + Φ hs + lg (sz (hps h) + sz hs + 1)`. -/
theorem phiList_cons_hp (h : Hp α) (hs : List (Hp α)) :
    phiList (h :: hs) = phiList (hps h) + phiList hs +
      Real.logb 2 ((szList (hps h) : ℝ) + (szList hs : ℝ) + 1) := by
  obtain ⟨x, hsl⟩ := h
  rw [phiList_cons, show hps (.mk x hsl) = hsl from rfl]

/-- AFP `link2`: `link` against a destructed second argument. -/
theorem link2 [LinearOrder α] (x : α) (lx : List (Hp α)) (h : Hp α) :
    link (.mk x lx) h = match h with
      | .mk y ly => if x < y then .mk x (.mk y ly :: lx) else .mk y (.mk x lx :: ly) := by
  obtain ⟨y, ly⟩ := h
  change link (.mk x lx) (.mk y ly) =
    if x < y then .mk x (.mk y ly :: lx) else .mk y (.mk x lx :: ly)
  by_cases hc : x < y
  · rw [link_eq_pos hc]; simp only [hc, ite_true]
  · rw [link_eq_neg hc]; simp only [hc, ite_false]

/-- AFP `T_link_0`, `T_insert_0`, `T_merge_0`. -/
theorem Tlink_eq_zero (h1 h2 : Hp α) : Tlink h1 h2 = 0 := rfl

theorem Tinsert_eq_zero (x : α) (ho : Heap α) : Tinsert x ho = 0 := rfl

theorem Tmerge_eq_zero (ho1 ho2 : Heap α) : Tmerge ho1 ho2 = 0 := rfl

/-- `lift_hp` from `Pairing_Heap_List2_Analysis.thy`: lift a function on
`Hp` to `Heap`, with a default value on `none`. -/
def liftHp {β : Type v} (c : β) (f : Hp α → β) : Heap α → β
  | none => c
  | some h => f h

/-- AFP `size_heap ≡ lift_hp 0 sz`. -/
theorem szHeap_eq_liftHp (ho : Heap α) : szHeap ho = liftHp 0 szHp ho := by
  cases ho <;> rfl

/-- AFP `Φ_heap ≡ lift_hp 0 Φ`. -/
theorem phiHeap_eq_liftHp (ho : Heap α) : phiHeap ho = liftHp 0 phiHp ho := by
  cases ho <;> rfl

end List2

end PairingHeap

end Cslib.Algorithms.Lean
