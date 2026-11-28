/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Joinable_BST_Work_Bounds/StronglyJoinableRBT.thy` (Archive of Formal Proofs, entry
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
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.RedBlackJoin
public import Mathlib.Tactic

/-!
# Joinable binary search trees: stored-height red–black join

The stored-black-height red–black `join` of Blelloch et al.: every node
stores its color together with its black height, read in constant time
instead of recomputed. `scol` / `sbh` / `sR` / `sB` / `sinvc` /
`sinvc2` / `sinvh` / `srbt`, the rebalancing helpers `sbaliL` /
`sbaliR`, `sjoinL` / `sjoinR` / `sblacken` / `sjoin` with `set` /
`bst` / `inv` / `tsize` correctness and the `JoinData` instance
`sjoinData`, the rank `srk` with its `rule_mono` / `rule_sub` lemmas,
the timing functions `TsjoinL` / `TsjoinR` / `Tsjoin` with the cost
rule, and the `StronglyJoinableData` instance `sStronglyJoinable`.

Two deviations from the Figure 10.4 join are essential here: `sblacken`
paints the root black only when it is red with a red child, and `sjoin`
combines two black inputs of equal black height with a *red* node; both
are necessary for the rank of a join to exceed the larger input rank by
at most one. The timing functions charge one unit for every call of
`sjoinL` / `sjoinR`, the stopping call included (as AFP's `time_fun`
does), and zero for non-recursive helpers and for the equal-height case.

## Provenance

`StronglyJoinableRBT.thy` in the AFP entry `Joinable_BST_Work_Bounds`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u} [LinearOrder α]

-- ## Red–black trees with stored black height (`StronglyJoinableRBT.thy`)
-- The `join` of Blelloch et al. stores the black height in every node and
-- reads it in constant time, so the metadata field holds the color
-- together with the black height. The library `Set2_Join_RBT` join
-- recomputes the black height on every step instead. Two further
-- deviations concern the root color: this `join` paints the root black
-- only when it is red with a red child, and combines two black inputs of
-- equal black height with a *red* node. Both are necessary for the rank
-- of a join to exceed the larger input rank by at most one.

/-- Color of a stored-height tree (`StronglyJoinableRBT.col`). -/
public def scol : Tree α (Color × ℕ) → Color
  | .Leaf => .Black
  | .Node _ kv _ => kv.2.1

/-- Stored black height (`StronglyJoinableRBT.bh`), read, not recomputed. -/
public def sbh : Tree α (Color × ℕ) → ℕ
  | .Leaf => 0
  | .Node _ kv _ => kv.2.2

/-- Red node constructor with stored height (`StronglyJoinableRBT.R`). -/
public def sR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    Tree α (Color × ℕ) :=
  .Node l (a, (.Red, sbh l)) r

/-- Black node constructor with stored height (`StronglyJoinableRBT.B`). -/
public def sB (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    Tree α (Color × ℕ) :=
  .Node l (a, (.Black, sbh l + 1)) r

/-- Color invariant for stored-height trees (`invc`). -/
public def sinvc : Tree α (Color × ℕ) → Prop
  | .Leaf => True
  | .Node l kv r =>
    (kv.2.1 = .Red → scol l = .Black ∧ scol r = .Black) ∧ sinvc l ∧ sinvc r

/-- Weaker color invariant (`invc2`): a red root may have a red child. -/
public def sinvc2 : Tree α (Color × ℕ) → Prop
  | .Leaf => True
  | .Node l _ r => sinvc l ∧ sinvc r

/-- Black-height invariant (`invh`): sibling black heights agree and the
stored height matches `sbh`. -/
public def sinvh : Tree α (Color × ℕ) → Prop
  | .Leaf => True
  | .Node l kv r =>
    sbh l = sbh r ∧ kv.2.2 = (if kv.2.1 = .Black then sbh l + 1 else sbh l) ∧ sinvh l ∧ sinvh r

/-- Stored-height red–black invariant (`rbt`): `invc ∧ invh`. -/
public def srbt (t : Tree α (Color × ℕ)) : Prop := sinvc t ∧ sinvh t

/-- `baliL` for stored black heights (same two red patterns, `sR`/`sB`
constructors). -/
public def sbaliL : Tree α (Color × ℕ) → α → Tree α (Color × ℕ) → Tree α (Color × ℕ)
  | .Node (.Node t1 (a, (.Red, _)) t2) (b, (.Red, _)) t3, c, t4 =>
    sR (sB t1 a t2) b (sB t3 c t4)
  | .Node t1 (a, (.Red, _)) (.Node t2 (b, (.Red, _)) t3), c, t4 =>
    sR (sB t1 a t2) b (sB t3 c t4)
  | t1, a, t2 => sB t1 a t2

/-- `baliR` for stored black heights. -/
public def sbaliR : Tree α (Color × ℕ) → α → Tree α (Color × ℕ) → Tree α (Color × ℕ)
  | t1, a, .Node t2 (b, (.Red, _)) (.Node t3 (c, (.Red, _)) t4) =>
    sR (sB t1 a t2) b (sB t3 c t4)
  | t1, a, .Node (.Node t2 (b, (.Red, _)) t3) (c, (.Red, _)) t4 =>
    sR (sB t1 a t2) b (sB t3 c t4)
  | t1, a, t2 => sB t1 a t2

/-- `set` for `sbaliL` (Isabelle `set_baliL`). -/
public theorem set_sbaliL (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    set_tree (sbaliL l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  cases l with
  | Leaf => simp [sbaliL, sB]
  | Node ll kv rl =>
    obtain ⟨a', ch⟩ := kv
    obtain ⟨c, _⟩ := ch
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf => simp [sbaliL, sB]
        | Node t2 kv2 t3 =>
          obtain ⟨b, ch2⟩ := kv2
          obtain ⟨c2, _⟩ := ch2
          cases c2 with
          | Red => simp only [sbaliL, sR, sB, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
          | Black => simp [sbaliL, sB]
      | Black => simp [sbaliL, sB]
    | Node t1 kv1 t2 =>
      obtain ⟨a1, ch1⟩ := kv1
      obtain ⟨c1, _⟩ := ch1
      cases c with
      | Red =>
        cases c1 with
        | Red => simp only [sbaliL, sR, sB, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
        | Black =>
          cases rl with
          | Leaf => simp [sbaliL, sB]
          | Node t2 kv2 t3 =>
            obtain ⟨b, ch2⟩ := kv2
            obtain ⟨c2, _⟩ := ch2
            cases c2 with
            | Red => simp only [sbaliL, sR, sB, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
            | Black => simp [sbaliL, sB]
      | Black => simp [sbaliL, sB]

/-- `set` for `sbaliR` (Isabelle `set_baliR`). -/
public theorem set_sbaliR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    set_tree (sbaliR l a r) = set_tree l ∪ {a} ∪ set_tree r := by
  cases r with
  | Leaf => simp [sbaliR, sB]
  | Node lr kv rr =>
    obtain ⟨b, ch⟩ := kv
    obtain ⟨c, _⟩ := ch
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases lr with
        | Leaf => simp [sbaliR, sB]
        | Node t2 kv2 t3 =>
          obtain ⟨b', ch2⟩ := kv2
          obtain ⟨c2, _⟩ := ch2
          cases c2 with
          | Red => simp only [sbaliR, sR, sB, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
          | Black => simp [sbaliR, sB]
      | Black => simp [sbaliR, sB]
    | Node t3 kv1 t4 =>
      obtain ⟨d, ch1⟩ := kv1
      obtain ⟨dc, _⟩ := ch1
      cases c with
      | Red =>
        cases dc with
        | Red => simp only [sbaliR, sR, sB, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
        | Black =>
          cases lr with
          | Leaf => simp [sbaliR, sB]
          | Node t2 kv2 t3 =>
            obtain ⟨b', ch2⟩ := kv2
            obtain ⟨c2, _⟩ := ch2
            cases c2 with
            | Red => simp only [sbaliR, sR, sB, set_tree]; ext y; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]; tauto
            | Black => simp [sbaliR, sB]
      | Black => simp [sbaliR, sB]

/-- `bst` for `sbaliL` (Isabelle `bst_baliL`). -/
public theorem bst_sbaliL (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ))
    (hbl : bst l) (hbr : bst r) (hl : ∀ x ∈ set_tree l, x < a)
    (hr : ∀ y ∈ set_tree r, a < y) : bst (sbaliL l a r) := by
  fun_cases sbaliL l a r <;> simp_all [bst, sR, sB, set_tree] <;> aesop (add unsafe lt_trans)

/-- `bst` for `sbaliR` (Isabelle `bst_baliR`). -/
public theorem bst_sbaliR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ))
    (hbl : bst l) (hbr : bst r) (hl : ∀ x ∈ set_tree l, x < a)
    (hr : ∀ y ∈ set_tree r, a < y) : bst (sbaliR l a r) := by
  fun_cases sbaliR l a r <;> simp_all [bst, sR, sB, set_tree] <;> aesop (add unsafe lt_trans)

/-- `tsize` for `sbaliL` (Isabelle `size_baliL`). -/
public theorem tsize_sbaliL (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    tsize (sbaliL l a r) = tsize l + tsize r + 1 := by
  fun_cases sbaliL l a r <;> simp [tsize, sR, sB] <;> omega

/-- `tsize` for `sbaliR` (Isabelle `size_baliR`). -/
public theorem tsize_sbaliR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    tsize (sbaliR l a r) = tsize l + tsize r + 1 := by
  fun_cases sbaliR l a r <;> simp [tsize, sR, sB] <;> omega

/-- Invariants for `sbaliL` (Isabelle `inv_baliL`). -/
public theorem sbaliL_inv (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ))
    (hinvh_l : sinvh l) (hinvh_r : sinvh r) (hinvc2 : sinvc2 l) (hinvc : sinvc r)
    (hbh : sbh l = sbh r) :
    sinvc (sbaliL l a r) ∧ sinvh (sbaliL l a r) ∧ sbh (sbaliL l a r) = sbh l + 1 := by
  cases l with
  | Leaf =>
    have heq : sbaliL (Tree.Leaf : Tree α (Color × ℕ)) a r = sB Tree.Leaf a r := rfl
    rw [heq]
    simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
  | Node ll kv rl =>
    obtain ⟨b, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    cases ll with
    | Leaf =>
      cases c with
      | Red =>
        cases rl with
        | Leaf =>
          have heq : sbaliL (Tree.Node Tree.Leaf (b, (.Red, h)) Tree.Leaf) a r =
              sB (Tree.Node Tree.Leaf (b, (.Red, h)) Tree.Leaf) a r := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', ch2⟩ := kv2
          obtain ⟨c2, h2⟩ := ch2
          cases c2 with
          | Red =>
            have heq : sbaliL (Tree.Node Tree.Leaf (b, (.Red, h)) (Tree.Node t2 (b', (.Red, h2)) t3)) a r =
                sR (sB Tree.Leaf b t2) b' (sB t3 a r) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
          | Black =>
            have heq : sbaliL (Tree.Node Tree.Leaf (b, (.Red, h)) (Tree.Node t2 (b', (.Black, h2)) t3)) a r =
                sB (Tree.Node Tree.Leaf (b, (.Red, h)) (Tree.Node t2 (b', (.Black, h2)) t3)) a r := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
      | Black =>
        have heq : sbaliL (Tree.Node Tree.Leaf (b, (.Black, h)) rl) a r =
            sB (Tree.Node Tree.Leaf (b, (.Black, h)) rl) a r := rfl
        rw [heq]
        simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
    | Node t1 kv1 t2 =>
      obtain ⟨a1, ch1⟩ := kv1
      obtain ⟨c1, h1⟩ := ch1
      cases c with
      | Red =>
        cases c1 with
        | Red =>
          have heq : sbaliL (Tree.Node (Tree.Node t1 (a1, (.Red, h1)) t2) (b, (.Red, h)) rl) a r =
              sR (sB t1 a1 t2) b (sB rl a r) := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Black =>
          cases rl with
          | Leaf =>
            have heq : sbaliL (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Red, h)) Tree.Leaf) a r =
                sB (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Red, h)) Tree.Leaf) a r := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', ch2'⟩ := kv2'
            obtain ⟨c2', h2'⟩ := ch2'
            cases c2' with
            | Red =>
              have heq : sbaliL (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Red, h)) (Tree.Node t2' (b', (.Red, h2')) t3')) a r =
                  sR (sB (Tree.Node t1 (a1, (.Black, h1)) t2) b t2') b' (sB t3' a r) := rfl
              rw [heq]
              simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
            | Black =>
              have heq : sbaliL (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Red, h)) (Tree.Node t2' (b', (.Black, h2')) t3')) a r =
                  sB (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Red, h)) (Tree.Node t2' (b', (.Black, h2')) t3')) a r := rfl
              rw [heq]
              simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
      | Black =>
        cases c1 with
        | Red =>
          have heq : sbaliL (Tree.Node (Tree.Node t1 (a1, (.Red, h1)) t2) (b, (.Black, h)) rl) a r =
              sB (Tree.Node (Tree.Node t1 (a1, (.Red, h1)) t2) (b, (.Black, h)) rl) a r := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Black =>
          have heq : sbaliL (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Black, h)) rl) a r =
              sB (Tree.Node (Tree.Node t1 (a1, (.Black, h1)) t2) (b, (.Black, h)) rl) a r := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega

/-- Invariants for `sbaliR` (Isabelle `inv_baliR`). -/
public theorem sbaliR_inv (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ))
    (hinvh_l : sinvh l) (hinvh_r : sinvh r) (hinvc : sinvc l) (hinvc2 : sinvc2 r)
    (hbh : sbh l = sbh r) :
    sinvc (sbaliR l a r) ∧ sinvh (sbaliR l a r) ∧ sbh (sbaliR l a r) = sbh l + 1 := by
  cases r with
  | Leaf =>
    have heq : sbaliR l a (Tree.Leaf : Tree α (Color × ℕ)) = sB l a Tree.Leaf := rfl
    rw [heq]
    simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
  | Node lr kv rr =>
    obtain ⟨b, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    cases rr with
    | Leaf =>
      cases c with
      | Red =>
        cases lr with
        | Leaf =>
          have heq : sbaliR l a (Tree.Node Tree.Leaf (b, (.Red, h)) Tree.Leaf) =
              sB l a (Tree.Node Tree.Leaf (b, (.Red, h)) Tree.Leaf) := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', ch2⟩ := kv2
          obtain ⟨c2, h2⟩ := ch2
          cases c2 with
          | Red =>
            have heq : sbaliR l a (Tree.Node (Tree.Node t2 (b', (.Red, h2)) t3) (b, (.Red, h)) Tree.Leaf) =
                sR (sB l a t2) b' (sB t3 b Tree.Leaf) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
          | Black =>
            have heq : sbaliR l a (Tree.Node (Tree.Node t2 (b', (.Black, h2)) t3) (b, (.Red, h)) Tree.Leaf) =
                sB l a (Tree.Node (Tree.Node t2 (b', (.Black, h2)) t3) (b, (.Red, h)) Tree.Leaf) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
      | Black =>
        cases lr with
        | Leaf =>
          have heq : sbaliR l a (Tree.Node Tree.Leaf (b, (.Black, h)) Tree.Leaf) =
              sB l a (Tree.Node Tree.Leaf (b, (.Black, h)) Tree.Leaf) := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Node t2 kv2 t3 =>
          obtain ⟨b', ch2⟩ := kv2
          obtain ⟨c2, h2⟩ := ch2
          cases c2 with
          | Red =>
            have heq : sbaliR l a (Tree.Node (Tree.Node t2 (b', (.Red, h2)) t3) (b, (.Black, h)) Tree.Leaf) =
                sB l a (Tree.Node (Tree.Node t2 (b', (.Red, h2)) t3) (b, (.Black, h)) Tree.Leaf) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
          | Black =>
            have heq : sbaliR l a (Tree.Node (Tree.Node t2 (b', (.Black, h2)) t3) (b, (.Black, h)) Tree.Leaf) =
                sB l a (Tree.Node (Tree.Node t2 (b', (.Black, h2)) t3) (b, (.Black, h)) Tree.Leaf) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
    | Node t3 kv1 t4 =>
      obtain ⟨d, ch1⟩ := kv1
      obtain ⟨dc, h1⟩ := ch1
      cases c with
      | Red =>
        cases dc with
        | Red =>
          have heq : sbaliR l a (Tree.Node lr (b, (.Red, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) =
              sR (sB l a lr) b (sB t3 d t4) := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Black =>
          cases lr with
          | Leaf =>
            have heq : sbaliR l a (Tree.Node Tree.Leaf (b, (.Red, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) =
                sB l a (Tree.Node Tree.Leaf (b, (.Red, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', ch2'⟩ := kv2'
            obtain ⟨c2', h2'⟩ := ch2'
            cases c2' with
            | Red =>
              have heq : sbaliR l a (Tree.Node (Tree.Node t2' (b', (.Red, h2')) t3') (b, (.Red, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) =
                  sR (sB l a t2') b' (sB t3' b (Tree.Node t3 (d, (.Black, h1)) t4)) := rfl
              rw [heq]
              simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
            | Black =>
              have heq : sbaliR l a (Tree.Node (Tree.Node t2' (b', (.Black, h2')) t3') (b, (.Red, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) =
                  sB l a (Tree.Node (Tree.Node t2' (b', (.Black, h2')) t3') (b, (.Red, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) := rfl
              rw [heq]
              simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
      | Black =>
        cases dc with
        | Red =>
          cases lr with
          | Leaf =>
            have heq : sbaliR l a (Tree.Node Tree.Leaf (b, (.Black, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) =
                sB l a (Tree.Node Tree.Leaf (b, (.Black, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) := rfl
            rw [heq]
            simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
          | Node t2' kv2' t3' =>
            obtain ⟨b', ch2'⟩ := kv2'
            obtain ⟨c2', h2'⟩ := ch2'
            cases c2' with
            | Red =>
              have heq : sbaliR l a (Tree.Node (Tree.Node t2' (b', (.Red, h2')) t3') (b, (.Black, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) =
                  sB l a (Tree.Node (Tree.Node t2' (b', (.Red, h2')) t3') (b, (.Black, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) := rfl
              rw [heq]
              simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
            | Black =>
              have heq : sbaliR l a (Tree.Node (Tree.Node t2' (b', (.Black, h2')) t3') (b, (.Black, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) =
                  sB l a (Tree.Node (Tree.Node t2' (b', (.Black, h2')) t3') (b, (.Black, h)) (Tree.Node t3 (d, (.Red, h1)) t4)) := rfl
              rw [heq]
              simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega
        | Black =>
          have heq : sbaliR l a (Tree.Node lr (b, (.Black, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) =
              sB l a (Tree.Node lr (b, (.Black, h)) (Tree.Node t3 (d, (.Black, h1)) t4)) := rfl
          rw [heq]
          simp_all [sinvc.eq_1, sinvc.eq_2, sinvc2.eq_1, sinvc2.eq_2, sinvh.eq_1, sinvh.eq_2, sbh.eq_1, sbh.eq_2, scol.eq_1, scol.eq_2, sR, sB] <;> try omega



/-- `set` for `sR` / `sB` (both are single `Node`s). -/
public theorem set_sR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    set_tree (sR l a r) = set_tree l ∪ {a} ∪ set_tree r := rfl

public theorem set_sB (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    set_tree (sB l a r) = set_tree l ∪ {a} ∪ set_tree r := rfl

/-- `sbh` / `scol` of `sR` / `sB` (definitional). -/
public theorem sbh_sR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    sbh (sR l a r) = sbh l := rfl

public theorem sbh_sB (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    sbh (sB l a r) = sbh l + 1 := rfl

public theorem scol_sR (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    scol (sR l a r) = .Red := rfl

public theorem scol_sB (l : Tree α (Color × ℕ)) (a : α) (r : Tree α (Color × ℕ)) :
    scol (sB l a r) = .Black := rfl

/-- `sinvc` / `sinvh` of `sB` / `sR` (helpers for `blacken` / `join`). -/
public theorem sinvc_sB {l r : Tree α (Color × ℕ)} {a : α} (hl : sinvc l) (hr : sinvc r) :
    sinvc (sB l a r) := by
  refine ⟨?_, hl, hr⟩
  intro h
  simp at h

public theorem sinvh_sB {l r : Tree α (Color × ℕ)} {a : α} (hl : sinvh l) (hr : sinvh r)
    (hb : sbh l = sbh r) : sinvh (sB l a r) :=
  ⟨hb, rfl, hl, hr⟩

public theorem sinvc_sR {l r : Tree α (Color × ℕ)} {a : α}
    (hc : scol l = .Black ∧ scol r = .Black) (hl : sinvc l) (hr : sinvc r) :
    sinvc (sR l a r) :=
  ⟨fun _ => hc, hl, hr⟩

public theorem sinvh_sR {l r : Tree α (Color × ℕ)} {a : α} (hl : sinvh l) (hr : sinvh r)
    (hb : sbh l = sbh r) : sinvh (sR l a r) :=
  ⟨hb, rfl, hl, hr⟩

/-- `sinvc` implies `sinvc2` (mirror of `invc2_of_invc`). -/
public theorem sinvc2_of_sinvc (t : Tree α (Color × ℕ)) (h : sinvc t) : sinvc2 t := by
  cases t with
  | Leaf => trivial
  | Node l kv r => exact ⟨h.2.1, h.2.2⟩

/-- `joinL` for stored black heights (`StronglyJoinableRBT.joinL`): descend
the left spine of `r` while `sbh r > sbh l`, rebalancing with `sbaliL`
at black nodes and `sR` at red nodes. -/
public def sjoinL : Tree α (Color × ℕ) → α → Tree α (Color × ℕ) → Tree α (Color × ℕ)
  | l, x, r =>
    if sbh r ≤ sbh l then sR l x r
    else match r with
      | .Leaf => sR l x .Leaf
      | .Node l' (x', (c, _)) r' =>
        if c = .Black then sbaliL (sjoinL l x l') x' r' else sR (sjoinL l x l') x' r'
termination_by l x r => r

/-- `joinR` for stored black heights (mirror of `sjoinL`). -/
public def sjoinR : Tree α (Color × ℕ) → α → Tree α (Color × ℕ) → Tree α (Color × ℕ)
  | l, x, r =>
    if sbh l ≤ sbh r then sR l x r
    else match l with
      | .Leaf => sR .Leaf x r
      | .Node l' (x', (c, _)) r' =>
        if c = .Black then sbaliR l' x' (sjoinR r' x r) else sR l' x' (sjoinR r' x r)
termination_by l x r => l

/-- `blacken`: paint the root black, but only when it is red with a red
child (`StronglyJoinableRBT.blacken`). -/
public def sblacken : Tree α (Color × ℕ) → Tree α (Color × ℕ)
  | .Node l (a, (.Red, h)) r =>
    if scol l = .Red ∨ scol r = .Red then sB l a r else .Node l (a, (.Red, h)) r
  | t => t

/-- `join` for stored black heights: descend into the taller side and
`blacken`, or combine two equal-height inputs with `sR` (both black)
resp. `sB` (otherwise). -/
public def sjoin (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    Tree α (Color × ℕ) :=
  if sbh r < sbh l then sblacken (sjoinR l x r)
  else if sbh l < sbh r then sblacken (sjoinL l x r)
  else if scol l = .Black ∧ scol r = .Black then sR l x r else sB l x r

/-- `set` for `sjoinL` (Isabelle `set_joinL`). -/
public theorem set_sjoinL (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    set_tree (sjoinL l x r) = set_tree l ∪ {x} ∪ set_tree r := by
  induction r generalizing l with
  | Leaf =>
    simp [sjoinL, sR, set_tree]
  | Node l' kv r' ih =>
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh l
    · simp only [sjoinL, ite_eq_left hb]
      ext y; simp only [sR, set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
    · simp only [sjoinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [set_sbaliL, ih]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
      | Red =>
        simp only [reduceCtorEq, ite_false]
        rw [set_sR, ih]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto

/-- `set` for `sjoinR` (Isabelle `set_joinR`). -/
public theorem set_sjoinR (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    set_tree (sjoinR l x r) = set_tree l ∪ {x} ∪ set_tree r := by
  induction l generalizing r with
  | Leaf =>
    simp [sjoinR, sR, set_tree]
  | Node l' kv r' ihl ihr =>
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh r
    · simp only [sjoinR, ite_eq_left hb]
      ext y; simp only [sR, set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
    · simp only [sjoinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [set_sbaliR, ihr]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto
      | Red =>
        simp only [reduceCtorEq, ite_false]
        rw [set_sR, ihr]
        ext y; simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] <;> try tauto

/-- `bst` for `sjoinL` (Isabelle `bst_joinL`). -/
public theorem bst_sjoinL (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (b : Color × ℕ) (h : bst (Tree.Node l (x, b) r)) : bst (sjoinL l x r) := by
  revert h
  induction r generalizing l with
  | Leaf =>
    intro h
    have heq : sjoinL l x (Tree.Leaf : Tree α (Color × ℕ)) = sR l x Tree.Leaf := by
      simp [sjoinL]
    rw [heq]
    exact bst_node.mpr ⟨h.1, trivial, h.2.2.1, by simp⟩
  | Node l' kv r' ih =>
    intro h
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    obtain ⟨hbl, hbr, hl, hr⟩ := h
    have hbl' : bst l' := hbr.1
    have hbr' : bst r' := hbr.2.1
    have hl' : ∀ y ∈ set_tree l', y < x' := hbr.2.2.1
    have hr' : ∀ y ∈ set_tree r', x' < y := hbr.2.2.2
    have hxx' : x < x' := hr x' (by
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
      exact Or.inl (Or.inr trivial))
    have hbst_node : bst (Tree.Node l (x, b) l') :=
      ⟨hbl, hbl', hl, fun y hy => hr y (by
        simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
        exact Or.inl (Or.inl hy))⟩
    have hjoinl : bst (sjoinL l x l') := ih l hbst_node
    have hbound : ∀ y ∈ set_tree (sjoinL l x l'), y < x' := by
      intro y hy
      rw [set_sjoinL] at hy
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
      rcases hy with (hy | rfl) | hy
      · exact lt_trans (hl y hy) hxx'
      · exact hxx'
      · exact hl' y hy
    have hr'_bound : ∀ y ∈ set_tree r', x' < y := hr'
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh l
    · simp only [sjoinL, ite_eq_left hb]
      exact bst_node.mpr ⟨hbl, hbr, hl, hr⟩
    · simp only [sjoinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        exact bst_sbaliL (sjoinL l x l') x' r' hjoinl hbr' hbound hr'_bound
      | Red =>
        simp only [reduceCtorEq, ite_false]
        exact bst_node.mpr ⟨hjoinl, hbr', hbound, hr'_bound⟩

/-- `bst` for `sjoinR` (Isabelle `bst_joinR`). -/
public theorem bst_sjoinR (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (b : Color × ℕ) (h : bst (Tree.Node l (x, b) r)) : bst (sjoinR l x r) := by
  revert h
  induction l generalizing r with
  | Leaf =>
    intro h
    have heq : sjoinR (Tree.Leaf : Tree α (Color × ℕ)) x r = sR Tree.Leaf x r := by
      simp [sjoinR]
    rw [heq]
    exact bst_node.mpr ⟨trivial, h.2.1, by simp, h.2.2.2⟩
  | Node l' kv r' ihl ihr =>
    intro h
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    obtain ⟨hbl, hbr, hl, hr⟩ := h
    have hbl' : bst l' := hbl.1
    have hbr' : bst r' := hbl.2.1
    have hl' : ∀ y ∈ set_tree l', y < x' := hbl.2.2.1
    have hr' : ∀ y ∈ set_tree r', x' < y := hbl.2.2.2
    have hxx' : x' < x := hl x' (by
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
      exact Or.inl (Or.inr trivial))
    have hbst_node : bst (Tree.Node r' (x, b) r) :=
      ⟨hbr', hbr, fun y hy => hl y (by
        simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff]
        exact Or.inr hy), hr⟩
    have hjoinr : bst (sjoinR r' x r) := ihr r hbst_node
    have hbound : ∀ y ∈ set_tree (sjoinR r' x r), x' < y := by
      intro y hy
      rw [set_sjoinR] at hy
      simp only [set_tree_node, Set.mem_union, Set.mem_singleton_iff] at hy
      rcases hy with (hy | rfl) | hy
      · exact hr' y hy
      · exact hxx'
      · exact lt_trans hxx' (hr y hy)
    have hl'_bound : ∀ y ∈ set_tree l', y < x' := hl'
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh r
    · simp only [sjoinR, ite_eq_left hb]
      exact bst_node.mpr ⟨hbl, hbr, hl, hr⟩
    · simp only [sjoinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        exact bst_sbaliR l' x' (sjoinR r' x r) hbl' hjoinr hl'_bound hbound
      | Red =>
        simp only [reduceCtorEq, ite_false]
        exact bst_node.mpr ⟨hbl', hjoinr, hl'_bound, hbound⟩

/-- Color of `sjoinL`: a red root is passed upwards unchanged
(Isabelle `col_joinL`). -/
public theorem col_sjoinL (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hbh : sbh l < sbh r) (hcol : scol r = .Red) : scol (sjoinL l x r) = .Red := by
  cases r with
  | Leaf =>
    exfalso
    have h0 : sbh (Tree.Leaf : Tree α (Color × ℕ)) = 0 := rfl
    omega
  | Node l' kv r' =>
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh l
    · exfalso; omega
    · simp only [sjoinL, ite_eq_right hb]
      cases c' with
      | Black => simp [scol] at hcol
      | Red =>
        simp only [reduceCtorEq, ite_false]
        rfl

/-- Color of `sjoinR` (Isabelle `col_joinR`). -/
public theorem col_sjoinR (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hbh : sbh r < sbh l) (hcol : scol l = .Red) : scol (sjoinR l x r) = .Red := by
  cases l with
  | Leaf =>
    exfalso
    have h0 : sbh (Tree.Leaf : Tree α (Color × ℕ)) = 0 := rfl
    omega
  | Node l' kv r' =>
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh r
    · exfalso; omega
    · simp only [sjoinR, ite_eq_right hb]
      cases c' with
      | Black => simp [scol] at hcol
      | Red =>
        simp only [reduceCtorEq, ite_false]
        rfl

/-- Invariants for `sjoinL` (Isabelle `inv_joinL`). -/
public theorem inv_sjoinL (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hinvc_l : sinvc l) (hinvc_r : sinvc r) (hinvh_l : sinvh l) (hinvh_r : sinvh r)
    (hbh : sbh l ≤ sbh r) :
    sinvc2 (sjoinL l x r) ∧ (sbh l ≠ sbh r ∧ scol r = .Black → sinvc (sjoinL l x r))
      ∧ sinvh (sjoinL l x r) ∧ sbh (sjoinL l x r) = sbh r := by
  revert hinvc_l hinvc_r hinvh_l hinvh_r hbh
  induction r generalizing l with
  | Leaf =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    have hbhl : sbh l = 0 := Nat.le_zero.mp hbh
    have heq : sjoinL l x (Tree.Leaf : Tree α (Color × ℕ)) = sR l x Tree.Leaf := by
      simp [sjoinL]
    rw [heq]
    refine ⟨⟨hinvc_l, trivial⟩, ?_, ⟨hbhl, rfl, hinvh_l, trivial⟩, hbhl⟩
    intro hcon
    exact False.elim (hcon.1 (hbhl.trans rfl))
  | Node l' kv r' ih =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    have hinvc_l' : sinvc l' := hinvc_r.2.1
    have hinvc_r' : sinvc r' := hinvc_r.2.2
    have hinvh_l' : sinvh l' := hinvh_r.2.2.1
    have hinvh_r' : sinvh r' := hinvh_r.2.2.2
    have hbh_lr : sbh l' = sbh r' := hinvh_r.1
    have hh' : h' = if c' = .Black then sbh l' + 1 else sbh l' := hinvh_r.2.1
    have hNode : sbh (Tree.Node l' (x', (c', h')) r') = h' := rfl
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh l
    · have hbh_eq : sbh l = sbh (Tree.Node l' (x', (c', h')) r') := by omega
      simp only [sjoinL, ite_eq_left hb]
      refine ⟨⟨hinvc_l, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbh_eq]),
        ⟨hbh_eq, rfl, hinvh_l, hinvh_r⟩, hbh_eq⟩
    · simp only [sjoinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true] at hh' ⊢
        have hbh_l' : sbh l ≤ sbh l' := by omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ :=
          ih l hinvc_l hinvc_l' hinvh_l hinvh_l' hbh_l'
        obtain ⟨hinvc_b, hinvh_b, hbh_b⟩ :=
          sbaliL_inv (sjoinL l x l') x' r' hinvh_j hinvh_r' hinvc2_j hinvc_r' (by omega)
        refine ⟨sinvc2_of_sinvc _ hinvc_b, fun _ => hinvc_b, hinvh_b, ?_⟩
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false] at hh' ⊢
        have hbh_l' : sbh l ≤ sbh l' := by omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ :=
          ih l hinvc_l hinvc_l' hinvh_l hinvh_l' hbh_l'
        have hbhR : sbh (sR (sjoinL l x l') x' r') = sbh (sjoinL l x l') := rfl
        have hcol_l' : scol l' = .Black := (hinvc_r.1 rfl).1
        have hinvc_j : sinvc (sjoinL l x l') :=
          hcond_j ⟨by omega, hcol_l'⟩
        refine ⟨⟨hinvc_j, hinvc_r'⟩, fun hcon => absurd hcon.2 (by simp [scol]),
          ⟨?_, ?_, hinvh_j, hinvh_r'⟩, ?_⟩
        · omega
        · rfl
        · rw [hbhR]; omega

/-- Invariants for `sjoinR` (Isabelle `inv_joinR`). -/
public theorem inv_sjoinR (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hinvc_l : sinvc l) (hinvc_r : sinvc r) (hinvh_l : sinvh l) (hinvh_r : sinvh r)
    (hbh : sbh r ≤ sbh l) :
    sinvc2 (sjoinR l x r) ∧ (sbh l ≠ sbh r ∧ scol l = .Black → sinvc (sjoinR l x r))
      ∧ sinvh (sjoinR l x r) ∧ sbh (sjoinR l x r) = sbh l := by
  revert hinvc_l hinvc_r hinvh_l hinvh_r hbh
  induction l generalizing r with
  | Leaf =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    have hbhr : sbh r = 0 := Nat.le_zero.mp hbh
    have heq : sjoinR (Tree.Leaf : Tree α (Color × ℕ)) x r = sR Tree.Leaf x r := by
      simp [sjoinR]
    rw [heq]
    refine ⟨⟨trivial, hinvc_r⟩, ?_, ⟨hbhr.symm, rfl, trivial, hinvh_r⟩, rfl⟩
    intro hcon
    exact False.elim (hcon.1 ((rfl : sbh Tree.Leaf = 0).trans hbhr.symm))
  | Node l' kv r' ihl ihr =>
    intro hinvc_l hinvc_r hinvh_l hinvh_r hbh
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    have hinvc_l' : sinvc l' := hinvc_l.2.1
    have hinvc_r' : sinvc r' := hinvc_l.2.2
    have hinvh_l' : sinvh l' := hinvh_l.2.2.1
    have hinvh_r' : sinvh r' := hinvh_l.2.2.2
    have hbh_lr : sbh l' = sbh r' := hinvh_l.1
    have hh' : h' = if c' = .Black then sbh l' + 1 else sbh l' := hinvh_l.2.1
    have hNode : sbh (Tree.Node l' (x', (c', h')) r') = h' := rfl
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh r
    · have hbh_eq : sbh (Tree.Node l' (x', (c', h')) r') = sbh r := by omega
      simp only [sjoinR, ite_eq_left hb]
      refine ⟨⟨hinvc_l, hinvc_r⟩, fun hcon => absurd hcon.1 (by simp [hbh_eq]),
        ⟨hbh_eq, rfl, hinvh_l, hinvh_r⟩, rfl⟩
    · simp only [sjoinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true] at hh' ⊢
        have hbh_r' : sbh r ≤ sbh r' := by omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ :=
          ihr r hinvc_r' hinvc_r hinvh_r' hinvh_r hbh_r'
        obtain ⟨hinvc_b, hinvh_b, hbh_b⟩ :=
          sbaliR_inv l' x' (sjoinR r' x r) hinvh_l' hinvh_j hinvc_l' hinvc2_j (by omega)
        refine ⟨sinvc2_of_sinvc _ hinvc_b, fun _ => hinvc_b, hinvh_b, ?_⟩
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false] at hh' ⊢
        have hbh_r' : sbh r ≤ sbh r' := by omega
        obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ :=
          ihr r hinvc_r' hinvc_r hinvh_r' hinvh_r hbh_r'
        have hbhR : sbh (sR l' x' (sjoinR r' x r)) = sbh l' := rfl
        have hcol_r' : scol r' = .Black := (hinvc_l.1 rfl).2
        have hinvc_j : sinvc (sjoinR r' x r) :=
          hcond_j ⟨by omega, hcol_r'⟩
        refine ⟨⟨hinvc_l', hinvc_j⟩, fun hcon => absurd hcon.2 (by simp [scol]),
          ⟨?_, ?_, hinvh_l', hinvh_j⟩, ?_⟩
        · omega
        · rfl
        · rw [hbhR]; omega

/-- `set` for `sblacken` (Isabelle `set_blacken`). -/
public theorem set_sblacken (t : Tree α (Color × ℕ)) : set_tree (sblacken t) = set_tree t := by
  cases t with
  | Leaf => rfl
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    cases c with
    | Black => rfl
    | Red =>
      by_cases hc : scol l = .Red ∨ scol r = .Red
      · have h1 : sblacken (Tree.Node l (a, (.Red, h)) r) = sB l a r := by
          simp [sblacken, hc]
        rw [h1, set_sB]
        rfl
      · have h1 : sblacken (Tree.Node l (a, (.Red, h)) r) =
            Tree.Node l (a, (.Red, h)) r := by
          simp [sblacken, hc]
        rw [h1]

/-- `bst` for `sblacken` (Isabelle `bst_blacken`). -/
public theorem bst_sblacken (t : Tree α (Color × ℕ)) : bst (sblacken t) = bst t := by
  cases t with
  | Leaf => rfl
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    cases c with
    | Black => rfl
    | Red =>
      by_cases hc : scol l = .Red ∨ scol r = .Red
      · simp only [sblacken, ite_eq_left hc]
        rfl
      · simp only [sblacken, ite_eq_right hc]

/-- Invariants for `sblacken` (Isabelle `inv_blacken`). -/
public theorem inv_sblacken (t : Tree α (Color × ℕ)) (h2 : sinvc2 t) (hh : sinvh t) :
    sinvc (sblacken t) ∧ sinvh (sblacken t) := by
  cases t with
  | Leaf => exact ⟨trivial, trivial⟩
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    have h2l : sinvc l := h2.1
    have h2r : sinvc r := h2.2
    have hhl : sinvh l := hh.2.2.1
    have hhr : sinvh r := hh.2.2.2
    have hbh : sbh l = sbh r := hh.1
    cases c with
    | Black =>
      exact ⟨⟨fun h => by simp at h, h2l, h2r⟩, hh⟩
    | Red =>
      by_cases hc : scol l = .Red ∨ scol r = .Red
      · have h1 : sblacken (Tree.Node l (a, (.Red, h)) r) = sB l a r := by
          simp [sblacken, hc]
        rw [h1]
        exact ⟨sinvc_sB h2l h2r, sinvh_sB hhl hhr hbh⟩
      · have h1 : sblacken (Tree.Node l (a, (.Red, h)) r) =
            Tree.Node l (a, (.Red, h)) r := by
          simp [sblacken, hc]
        rw [h1]
        have hcol : scol l = .Black ∧ scol r = .Black := by
          constructor
          · cases h : scol l with
            | Black => rfl
            | Red => exact absurd (Or.inl h) hc
          · cases h : scol r with
            | Black => rfl
            | Red => exact absurd (Or.inr h) hc
        exact ⟨⟨fun _ => hcol, h2l, h2r⟩, hh⟩

/-- `sblacken` is the identity on already-`sinvc` trees (Isabelle `blacken_id`). -/
public theorem sblacken_id (t : Tree α (Color × ℕ)) (h : sinvc t) : sblacken t = t := by
  cases t with
  | Leaf => rfl
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    cases c with
    | Black => rfl
    | Red =>
      have hcol : scol l = .Black ∧ scol r = .Black := (h.1 rfl)
      simp [sblacken, hcol.1, hcol.2]

/-- `set` for `sjoin` (Isabelle `set_join`). -/
public theorem set_sjoin (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    set_tree (sjoin l x r) = set_tree l ∪ {x} ∪ set_tree r := by
  by_cases h1 : sbh r < sbh l
  · have hjoin : sjoin l x r = sblacken (sjoinR l x r) := by simp [sjoin, h1]
    rw [hjoin, set_sblacken, set_sjoinR]
  · by_cases h2 : sbh l < sbh r
    · have hjoin : sjoin l x r = sblacken (sjoinL l x r) := by simp [sjoin, h1, h2]
      rw [hjoin, set_sblacken, set_sjoinL]
    · have hjoin : sjoin l x r =
          (if scol l = .Black ∧ scol r = .Black then sR l x r else sB l x r) := by
        simp [sjoin, h1, h2]
      rw [hjoin]
      by_cases h3 : scol l = .Black ∧ scol r = .Black
      · rw [ite_eq_left h3, set_sR]
      · rw [ite_eq_right h3, set_sB]

/-- `bst` for `sjoin` (Isabelle `bst_join`). -/
public theorem bst_sjoin (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (b : Color × ℕ) (h : bst (Tree.Node l (x, b) r)) : bst (sjoin l x r) := by
  by_cases h1 : sbh r < sbh l
  · have hjoin : sjoin l x r = sblacken (sjoinR l x r) := by simp [sjoin, h1]
    rw [hjoin, bst_sblacken]
    exact bst_sjoinR l x r b h
  · by_cases h2 : sbh l < sbh r
    · have hjoin : sjoin l x r = sblacken (sjoinL l x r) := by simp [sjoin, h1, h2]
      rw [hjoin, bst_sblacken]
      exact bst_sjoinL l x r b h
    · have hjoin : sjoin l x r =
          (if scol l = .Black ∧ scol r = .Black then sR l x r else sB l x r) := by
        simp [sjoin, h1, h2]
      rw [hjoin]
      by_cases h3 : scol l = .Black ∧ scol r = .Black
      · rw [ite_eq_left h3]
        exact bst_node.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      · rw [ite_eq_right h3]
        exact bst_node.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Invariants for `sjoin` (Isabelle `inv_join`). -/
public theorem inv_sjoin (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hinv_l : srbt l) (hinv_r : srbt r) : srbt (sjoin l x r) := by
  by_cases h1 : sbh r < sbh l
  · have hjoin : sjoin l x r = sblacken (sjoinR l x r) := by simp [sjoin, h1]
    rw [hjoin]
    obtain ⟨hinvc2_j, -, hinvh_j, -⟩ :=
      inv_sjoinR l x r hinv_l.1 hinv_r.1 hinv_l.2 hinv_r.2 (le_of_lt h1)
    exact inv_sblacken _ hinvc2_j hinvh_j
  · by_cases h2 : sbh l < sbh r
    · have hjoin : sjoin l x r = sblacken (sjoinL l x r) := by simp [sjoin, h1, h2]
      rw [hjoin]
      obtain ⟨hinvc2_j, -, hinvh_j, -⟩ :=
        inv_sjoinL l x r hinv_l.1 hinv_r.1 hinv_l.2 hinv_r.2 (le_of_lt h2)
      exact inv_sblacken _ hinvc2_j hinvh_j
    · have hbh : sbh l = sbh r := by omega
      have hjoin : sjoin l x r =
          (if scol l = .Black ∧ scol r = .Black then sR l x r else sB l x r) := by
        simp [sjoin, h1, h2]
      rw [hjoin]
      by_cases h3 : scol l = .Black ∧ scol r = .Black
      · rw [ite_eq_left h3]
        exact ⟨sinvc_sR h3 hinv_l.1 hinv_r.1, sinvh_sR hinv_l.2 hinv_r.2 hbh⟩
      · rw [ite_eq_right h3]
        exact ⟨sinvc_sB hinv_l.1 hinv_r.1, sinvh_sB hinv_l.2 hinv_r.2 hbh⟩

/-- Node count for `sjoinL` (Isabelle `size_joinL`). -/
public theorem tsize_sjoinL (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    tsize (sjoinL l x r) = tsize l + tsize r + 1 := by
  induction r generalizing l with
  | Leaf =>
    simp [sjoinL, tsize, sR]
  | Node l' kv r' ih =>
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh l
    · simp only [sjoinL, ite_eq_left hb]
      simp [tsize, sR]
    · simp only [sjoinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [tsize_sbaliL, ih]
        simp [tsize]
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have h : tsize (sR (sjoinL l x l') x' r') = tsize (sjoinL l x l') + tsize r' + 1 := rfl
        rw [h, ih]
        simp [tsize]
        omega

/-- Node count for `sjoinR` (Isabelle `size_joinR`). -/
public theorem tsize_sjoinR (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    tsize (sjoinR l x r) = tsize l + tsize r + 1 := by
  induction l generalizing r with
  | Leaf =>
    simp [sjoinR, tsize, sR]
  | Node l' kv r' ihl ihr =>
    obtain ⟨x', ch⟩ := kv
    obtain ⟨c', h'⟩ := ch
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh r
    · simp only [sjoinR, ite_eq_left hb]
      simp [tsize, sR]
    · simp only [sjoinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true]
        rw [tsize_sbaliR, ihr]
        simp [tsize]
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false]
        have h : tsize (sR l' x' (sjoinR r' x r)) = tsize l' + tsize (sjoinR r' x r) + 1 := rfl
        rw [h, ihr]
        simp [tsize]
        omega

/-- Node count for `sblacken` (Isabelle `size_blacken`). -/
public theorem tsize_sblacken (t : Tree α (Color × ℕ)) : tsize (sblacken t) = tsize t := by
  cases t with
  | Leaf => rfl
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv
    obtain ⟨c, h⟩ := ch
    cases c with
    | Black => rfl
    | Red =>
      by_cases hc : scol l = .Red ∨ scol r = .Red
      · simp only [sblacken, ite_eq_left hc]
        rfl
      · simp only [sblacken, ite_eq_right hc]

/-- Node count for `sjoin` (Isabelle `join_size`). -/
public theorem tsize_sjoin (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) :
    tsize (sjoin l x r) = tsize l + tsize r + 1 := by
  by_cases h1 : sbh r < sbh l
  · have hjoin : sjoin l x r = sblacken (sjoinR l x r) := by simp [sjoin, h1]
    rw [hjoin, tsize_sblacken, tsize_sjoinR]
  · by_cases h2 : sbh l < sbh r
    · have hjoin : sjoin l x r = sblacken (sjoinL l x r) := by simp [sjoin, h1, h2]
      rw [hjoin, tsize_sblacken, tsize_sjoinL]
    · have hjoin : sjoin l x r =
          (if scol l = .Black ∧ scol r = .Black then sR l x r else sB l x r) := by
        simp [sjoin, h1, h2]
      rw [hjoin]
      by_cases h3 : scol l = .Black ∧ scol r = .Black
      · rw [ite_eq_left h3]
        rfl
      · rw [ite_eq_right h3]
        rfl

/-- The stored-height red–black `JoinData` instance (`Set2_Join`, `tree_rb`). -/
public def sjoinData : JoinData α (Color × ℕ) where
  join := sjoin
  inv := srbt
  inv_leaf := ⟨trivial, trivial⟩
  set_join := fun l x r => set_sjoin l x r
  bst_join := fun l x b r h => bst_sjoin l x r b h
  inv_join := fun l x r hinv_l hinv_r => inv_sjoin l x r hinv_l hinv_r
  inv_node := fun l kv r h => ⟨⟨h.1.2.1, h.2.2.2.1⟩, ⟨h.1.2.2, h.2.2.2.2⟩⟩



/-- The rank of a stored-height red–black tree (AFP `rk`): twice the stored
black height, plus one for a red root. -/
public def srk (t : Tree α (Color × ℕ)) : ℕ := 2 * sbh t + (if scol t = .Red then 1 else 0)

/-- The rank is sandwiched between `2 * sbh t` and `2 * sbh t + 1`. -/
public theorem srk_bounds (t : Tree α (Color × ℕ)) :
    2 * sbh t ≤ srk t ∧ srk t ≤ 2 * sbh t + 1 := by
  cases t with
  | Leaf => exact ⟨le_refl 0, Nat.zero_le _⟩
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv; obtain ⟨c, hst⟩ := ch
    cases c with
    | Black =>
      constructor <;> simp only [srk, sbh, scol, reduceCtorEq, ite_false] <;> omega
    | Red =>
      constructor <;> simp only [srk, sbh, scol, eq_self_iff_true, ite_true] <;> omega

/-- Rank of a black-rooted tree. -/
public theorem srk_of_scol_black (t : Tree α (Color × ℕ)) (h : scol t = .Black) :
    srk t = 2 * sbh t := by
  cases t with
  | Leaf => rfl
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv; obtain ⟨c, hst⟩ := ch
    have hc : c = .Black := h
    rw [hc]
    rfl

/-- Rank of a red-rooted tree. -/
public theorem srk_of_scol_red (t : Tree α (Color × ℕ)) (h : scol t = .Red) :
    srk t = 2 * sbh t + 1 := by
  cases t with
  | Leaf => simp [scol] at h
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv; obtain ⟨c, hst⟩ := ch
    have hc : c = .Red := h
    rw [hc]
    rfl

/-- The balancing rule for the rank (AFP `rk_children`): the rank of a
well-formed node is at least one more than the max of the children's
ranks, and at most two more than the min. -/
public theorem srk_children {l r : Tree α (Color × ℕ)} {a : α} {c : Color} {hst : ℕ}
    (h : srbt (Tree.Node l (a, (c, hst)) r)) :
    max (srk l) (srk r) + 1 ≤ srk (Tree.Node l (a, (c, hst)) r) ∧
    srk (Tree.Node l (a, (c, hst)) r) ≤ min (srk l) (srk r) + 2 := by
  have hb : sbh l = sbh r := h.2.1
  have hsto : hst = if c = .Black then sbh l + 1 else sbh l := h.2.2.1
  have hsinvc : c = .Red → scol l = .Black ∧ scol r = .Black := h.1.1
  cases c with
  | Black =>
    simp only [eq_self_iff_true, ite_true] at hsto
    cases hc1 : scol l with
    | Black =>
      cases hc2 : scol r with
      | Black =>
        simp only [srk, sbh.eq_2, scol.eq_2, hc1, hc2, eq_self_iff_true, ite_true,
          reduceCtorEq, ite_false]
        omega
      | Red =>
        simp only [srk, sbh.eq_2, scol.eq_2, hc1, hc2, eq_self_iff_true, ite_true,
          reduceCtorEq, ite_false]
        omega
    | Red =>
      cases hc2 : scol r with
      | Black =>
        simp only [srk, sbh.eq_2, scol.eq_2, hc1, hc2, eq_self_iff_true, ite_true,
          reduceCtorEq, ite_false]
        omega
      | Red =>
        simp only [srk, sbh.eq_2, scol.eq_2, hc1, hc2, eq_self_iff_true, ite_true,
          reduceCtorEq, ite_false]
        omega
  | Red =>
    simp only [reduceCtorEq, ite_false] at hsto
    have hcol := hsinvc rfl
    simp only [srk, sbh.eq_2, scol.eq_2, hcol.1, hcol.2, eq_self_iff_true, ite_true,
      reduceCtorEq, ite_false]
    omega

/-- Every well-formed stored-height red–black tree satisfies the balancing
rule (AFP `rule_bal`). -/
public theorem srbt_rule_bal (t : Tree α (Color × ℕ)) (h : srbt t) :
    balancedOf (fun t => (srk t : ℝ)) 1 2 t := by
  induction t with
  | Leaf => trivial
  | Node l kv r ihl ihr =>
    obtain ⟨a, ch⟩ := kv
    obtain ⟨c, hst⟩ := ch
    have hchildren := srk_children h
    show max ((srk l : ℝ)) ((srk r : ℝ)) + 1 ≤ (srk (Tree.Node l (a, (c, hst)) r) : ℝ) ∧
      (srk (Tree.Node l (a, (c, hst)) r) : ℝ) ≤ min ((srk l : ℝ)) ((srk r : ℝ)) + 2 ∧
      balancedOf (fun t => (srk t : ℝ)) 1 2 l ∧ balancedOf (fun t => (srk t : ℝ)) 1 2 r
    refine ⟨by exact_mod_cast hchildren.1, by exact_mod_cast hchildren.2,
      ihl ⟨h.1.2.1, h.2.2.2.1⟩, ihr ⟨h.1.2.2, h.2.2.2.2⟩⟩

/-- Rank of `sblacken` (AFP `rk_blacken`). -/
public theorem srk_sblacken (t : Tree α (Color × ℕ)) (h : sinvh t) :
    srk t ≤ srk (sblacken t) ∧ srk (sblacken t) ≤ 2 * sbh t + 2 := by
  cases t with
  | Leaf => exact ⟨le_refl 0, Nat.zero_le _⟩
  | Node l kv r =>
    obtain ⟨a, ch⟩ := kv; obtain ⟨c, hst⟩ := ch
    have hb : sbh l = sbh r := h.1
    have hsto : hst = if c = .Black then sbh l + 1 else sbh l := h.2.1
    cases c with
    | Black =>
      simp only [eq_self_iff_true, ite_true] at hsto
      have e : srk (sblacken (Tree.Node l (a, (.Black, hst)) r)) = 2 * hst := rfl
      have e2 : srk (Tree.Node l (a, (.Black, hst)) r) = 2 * hst := rfl
      have e3 : sbh (Tree.Node l (a, (.Black, hst)) r) = hst := rfl
      rw [e, e2, e3]
      exact ⟨le_refl _, by omega⟩
    | Red =>
      simp only [reduceCtorEq, ite_false] at hsto
      by_cases hc : scol l = .Red ∨ scol r = .Red
      · have h1 : sblacken (Tree.Node l (a, (.Red, hst)) r) = sB l a r := by
          simp [sblacken, hc]
        rw [h1]
        simp only [srk, sB, sbh.eq_2, scol.eq_2, reduceCtorEq, ite_false, eq_self_iff_true,
          ite_true]
        omega
      · have h1 : sblacken (Tree.Node l (a, (.Red, hst)) r) =
            Tree.Node l (a, (.Red, hst)) r := by
          simp [sblacken, hc]
        rw [h1]
        simp only [srk, sbh.eq_2, scol.eq_2, eq_self_iff_true, ite_true]
        omega

/-- Rank of `blacken (joinR …)` (AFP `rk_joinR`). -/
public theorem srk_sjoinR (l r : Tree α (Color × ℕ)) (x : α) (hl : srbt l) (hr : srbt r)
    (hbh : sbh r < sbh l) :
    max (srk l) (srk r) ≤ srk (sblacken (sjoinR l x r)) ∧
    srk (sblacken (sjoinR l x r)) ≤ max (srk l) (srk r) + 1 := by
  obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ :=
    inv_sjoinR l x r hl.1 hr.1 hl.2 hr.2 (le_of_lt hbh)
  have hsrk_t : srk (sjoinR l x r) =
      2 * sbh l + (if scol (sjoinR l x r) = .Red then 1 else 0) := by
    simp only [srk]
    rw [hbh_j]
  have hsrk_r : srk r ≤ 2 * sbh l := by
    have hb2 := (srk_bounds r).2
    omega
  have hbl := srk_sblacken (sjoinR l x r) hinvh_j
  cases hc : scol l with
  | Red =>
    have hsrk_l : srk l = 2 * sbh l + 1 := srk_of_scol_red l hc
    have hcol_j : scol (sjoinR l x r) = .Red := col_sjoinR l x r hbh hc
    rw [hcol_j] at hsrk_t
    simp only [eq_self_iff_true, ite_true] at hsrk_t
    constructor <;> omega
  | Black =>
    have hsrk_l : srk l = 2 * sbh l := srk_of_scol_black l hc
    have hsinvc_j : sinvc (sjoinR l x r) :=
      hcond_j ⟨by omega, hc⟩
    have hid : sblacken (sjoinR l x r) = sjoinR l x r := sblacken_id _ hsinvc_j
    rw [hid]
    have hif : (if scol (sjoinR l x r) = .Red then (1:ℕ) else 0) ≤ 1 := by
      split <;> omega
    constructor <;> omega

/-- Rank of `blacken (joinL …)` (AFP `rk_joinL`). -/
public theorem srk_sjoinL (l r : Tree α (Color × ℕ)) (x : α) (hl : srbt l) (hr : srbt r)
    (hbh : sbh l < sbh r) :
    max (srk l) (srk r) ≤ srk (sblacken (sjoinL l x r)) ∧
    srk (sblacken (sjoinL l x r)) ≤ max (srk l) (srk r) + 1 := by
  obtain ⟨hinvc2_j, hcond_j, hinvh_j, hbh_j⟩ :=
    inv_sjoinL l x r hl.1 hr.1 hl.2 hr.2 (le_of_lt hbh)
  have hsrk_t : srk (sjoinL l x r) =
      2 * sbh r + (if scol (sjoinL l x r) = .Red then 1 else 0) := by
    simp only [srk]
    rw [hbh_j]
  have hsrk_l : srk l ≤ 2 * sbh r := by
    have hb2 := (srk_bounds l).2
    omega
  have hbl := srk_sblacken (sjoinL l x r) hinvh_j
  cases hc : scol r with
  | Red =>
    have hsrk_r : srk r = 2 * sbh r + 1 := srk_of_scol_red r hc
    have hcol_j : scol (sjoinL l x r) = .Red := col_sjoinL l x r hbh hc
    rw [hcol_j] at hsrk_t
    simp only [eq_self_iff_true, ite_true] at hsrk_t
    constructor <;> omega
  | Black =>
    have hsrk_r : srk r = 2 * sbh r := srk_of_scol_black r hc
    have hsinvc_j : sinvc (sjoinL l x r) :=
      hcond_j ⟨by omega, hc⟩
    have hid : sblacken (sjoinL l x r) = sjoinL l x r := sblacken_id _ hsinvc_j
    rw [hid]
    have hif : (if scol (sjoinL l x r) = .Red then (1:ℕ) else 0) ≤ 1 := by
      split <;> omega
    constructor <;> omega

/-- Rank of `join` (AFP `rk_join`). -/
public theorem srk_sjoin (l r : Tree α (Color × ℕ)) (x : α) (hl : srbt l) (hr : srbt r) :
    max (srk l) (srk r) ≤ srk (sjoin l x r) ∧
    srk (sjoin l x r) ≤ max (srk l) (srk r) + 1 := by
  rcases lt_trichotomy (sbh r) (sbh l) with h1 | h1 | h1
  · have hjoin : sjoin l x r = sblacken (sjoinR l x r) := by simp [sjoin, h1]
    rw [hjoin]
    exact srk_sjoinR l r x hl hr h1
  · have hbh : sbh l = sbh r := h1.symm
    have hjoin : sjoin l x r =
        (if scol l = .Black ∧ scol r = .Black then sR l x r else sB l x r) := by
      simp [sjoin, show ¬ sbh r < sbh l by omega, show ¬ sbh l < sbh r by omega]
    rw [hjoin]
    by_cases hc1 : scol l = .Black
    · by_cases hc2 : scol r = .Black
      · rw [ite_eq_left ⟨hc1, hc2⟩]
        have e1 : srk l = 2 * sbh l := srk_of_scol_black l hc1
        have e2 : srk r = 2 * sbh r := srk_of_scol_black r hc2
        have e3 : srk (sR l x r) = 2 * sbh l + 1 := rfl
        constructor <;> omega
      · have hc2' : scol r = .Red := by
          cases h : scol r with
          | Black => exact absurd h hc2
          | Red => rfl
        rw [ite_eq_right (by simp [hc1, hc2'])]
        have e1 : srk l = 2 * sbh l := srk_of_scol_black l hc1
        have e2 : srk r = 2 * sbh r + 1 := srk_of_scol_red r hc2'
        have e3 : srk (sB l x r) = 2 * (sbh l + 1) := rfl
        constructor <;> omega
    · have hc1' : scol l = .Red := by
        cases h : scol l with
        | Black => exact absurd h hc1
        | Red => rfl
      by_cases hc2 : scol r = .Black
      · rw [ite_eq_right (by simp [hc1', hc2])]
        have e1 : srk l = 2 * sbh l + 1 := srk_of_scol_red l hc1'
        have e2 : srk r = 2 * sbh r := srk_of_scol_black r hc2
        have e3 : srk (sB l x r) = 2 * (sbh l + 1) := rfl
        constructor <;> omega
      · have hc2' : scol r = .Red := by
          cases h : scol r with
          | Black => exact absurd h hc2
          | Red => rfl
        rw [ite_eq_right (by simp [hc1', hc2'])]
        have e1 : srk l = 2 * sbh l + 1 := srk_of_scol_red l hc1'
        have e2 : srk r = 2 * sbh r + 1 := srk_of_scol_red r hc2'
        have e3 : srk (sB l x r) = 2 * (sbh l + 1) := rfl
        constructor <;> omega
  · have hjoin : sjoin l x r = sblacken (sjoinL l x r) := by
      simp [sjoin, show ¬ sbh r < sbh l by omega, show sbh l < sbh r from h1]
    rw [hjoin]
    exact srk_sjoinL l r x hl hr h1

/-- Monotonicity rule for the rank (AFP `rule_mono`). -/
public theorem srbt_rule_mono {l r : Tree α (Color × ℕ)} {a : α} (hl : srbt l) (hr : srbt r) :
    max ((srk l : ℝ)) ((srk r : ℝ)) ≤ (srk (sjoin l a r) : ℝ) := by
  exact_mod_cast (srk_sjoin l r a hl hr).1

/-- Submodularity rule for the rank (AFP `rule_sub`). -/
public theorem srbt_rule_sub {l' l r' r : Tree α (Color × ℕ)} {a : α} {b : Color × ℕ} {x : ℝ}
    (h1 : (srk l' : ℝ) ≤ (srk l : ℝ) + x) (h2 : (srk r' : ℝ) ≤ (srk r : ℝ) + x)
    (hl' : srbt l') (hr' : srbt r') (hnode : srbt (Tree.Node l (a, b) r)) :
    (srk (sjoin l' a r') : ℝ) ≤ (srk (Tree.Node l (a, b) r) : ℝ) + x := by
  obtain ⟨c, hst⟩ := b
  have hub : (srk (sjoin l' a r') : ℝ) ≤ max ((srk l' : ℝ)) ((srk r' : ℝ)) + 1 := by
    exact_mod_cast (srk_sjoin l' r' a hl' hr').2
  have hmax : max ((srk l' : ℝ)) ((srk r' : ℝ)) ≤ max ((srk l : ℝ)) ((srk r : ℝ)) + x := by
    apply max_le
    · calc (srk l' : ℝ) ≤ (srk l : ℝ) + x := h1
        _ ≤ max ((srk l : ℝ)) ((srk r : ℝ)) + x := by
            exact add_le_add (le_max_left _ _) (le_refl x)
    · calc (srk r' : ℝ) ≤ (srk r : ℝ) + x := h2
        _ ≤ max ((srk l : ℝ)) ((srk r : ℝ)) + x := by
            exact add_le_add (le_max_right _ _) (le_refl x)
  have hchild : max ((srk l : ℝ)) ((srk r : ℝ)) + 1 ≤
      (srk (Tree.Node l (a, (c, hst)) r) : ℝ) := by
    exact_mod_cast (srk_children hnode).1
  linarith

/-- Timing function for `sjoinL` (AFP `T_joinL`): every invocation, the
stopping one included, costs one, as AFP's `time_fun` charges every call;
the helpers `sbh` / `scol` / `sbaliL` cost 0. -/
public def TsjoinL : Tree α (Color × ℕ) → α → Tree α (Color × ℕ) → ℕ
  | l, x, r =>
    if sbh r ≤ sbh l then 1
    else match r with
      | .Leaf => 1
      | .Node l' (x', (c, _)) r' => TsjoinL l x l' + 1
termination_by l x r => r

/-- Timing function for `sjoinR` (AFP `T_joinR`, mirror of `TsjoinL`):
every invocation, the stopping one included, costs one. -/
public def TsjoinR : Tree α (Color × ℕ) → α → Tree α (Color × ℕ) → ℕ
  | l, x, r =>
    if sbh l ≤ sbh r then 1
    else match l with
      | .Leaf => 1
      | .Node l' (x', (c, _)) r' => TsjoinR r' x r + 1
termination_by l x r => l

/-- Timing function for `sjoin` (AFP `T_join`): the `sblacken` and the
equal-height case cost 0. -/
public def Tsjoin (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ)) : ℕ :=
  if sbh r < sbh l then TsjoinR l x r
  else if sbh l < sbh r then TsjoinL l x r
  else 0

/-- Bound for `TsjoinL` (AFP `T_joinL`). -/
public theorem TsjoinL_bound (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hinvc_r : sinvc r) (hinvh_r : sinvh r) (hbh : sbh l ≤ sbh r) :
    TsjoinL l x r + 2 * sbh l ≤ 2 * sbh r + 1 + (if scol r = .Red then 1 else 0) := by
  revert hinvc_r hinvh_r hbh
  induction r generalizing l with
  | Leaf =>
    intro hinvc_r hinvh_r hbh
    have h0 : sbh (Tree.Leaf : Tree α (Color × ℕ)) = 0 := rfl
    have hT : TsjoinL l x (Tree.Leaf : Tree α (Color × ℕ)) = 1 := by
      simp only [TsjoinL, sbh.eq_1, Nat.zero_le, ite_true]
    rw [hT]
    simp only [sbh.eq_1, scol.eq_1, reduceCtorEq, ite_false]
    omega
  | Node l' kv r' ih =>
    intro hinvc_r hinvh_r hbh
    obtain ⟨x', ch⟩ := kv; obtain ⟨c', h'⟩ := ch
    have hinvc_l' : sinvc l' := hinvc_r.2.1
    have hinvh_l' : sinvh l' := hinvh_r.2.2.1
    have hbh_lr : sbh l' = sbh r' := hinvh_r.1
    have hh' : h' = if c' = .Black then sbh l' + 1 else sbh l' := hinvh_r.2.1
    have hNode : sbh (Tree.Node l' (x', (c', h')) r') = h' := rfl
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh l
    · simp only [TsjoinL, ite_eq_left hb]
      omega
    · simp only [TsjoinL, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true] at hh'
        simp only [scol.eq_2, reduceCtorEq, ite_false]
        have hbh_l' : sbh l ≤ sbh l' := by omega
        have hIH := ih l hinvc_l' hinvh_l' hbh_l'
        have hX : (if scol l' = .Red then (1:ℕ) else 0) ≤ 1 := by split <;> omega
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false] at hh'
        simp only [scol.eq_2, eq_self_iff_true, ite_true]
        have hcol_l' : scol l' = .Black := (hinvc_r.1 rfl).1
        have hbh_l' : sbh l ≤ sbh l' := by omega
        have hIH := ih l hinvc_l' hinvh_l' hbh_l'
        have hX : (if scol l' = .Red then (1:ℕ) else 0) = 0 := by simp [hcol_l']
        omega

/-- Bound for `TsjoinR` (AFP `T_joinR`). -/
public theorem TsjoinR_bound (l : Tree α (Color × ℕ)) (x : α) (r : Tree α (Color × ℕ))
    (hinvc_l : sinvc l) (hinvh_l : sinvh l) (hbh : sbh r ≤ sbh l) :
    TsjoinR l x r + 2 * sbh r ≤ 2 * sbh l + 1 + (if scol l = .Red then 1 else 0) := by
  revert hinvc_l hinvh_l hbh
  induction l generalizing r with
  | Leaf =>
    intro hinvc_l hinvh_l hbh
    have h0 : sbh (Tree.Leaf : Tree α (Color × ℕ)) = 0 := rfl
    have hT : TsjoinR (Tree.Leaf : Tree α (Color × ℕ)) x r = 1 := by
      simp only [TsjoinR, sbh.eq_1, Nat.zero_le, ite_true]
    rw [hT]
    simp only [sbh.eq_1, scol.eq_1, reduceCtorEq, ite_false]
    omega
  | Node l' kv r' ihl ihr =>
    intro hinvc_l hinvh_l hbh
    obtain ⟨x', ch⟩ := kv; obtain ⟨c', h'⟩ := ch
    have hinvc_r' : sinvc r' := hinvc_l.2.2
    have hinvh_r' : sinvh r' := hinvh_l.2.2.2
    have hbh_lr : sbh l' = sbh r' := hinvh_l.1
    have hh' : h' = if c' = .Black then sbh l' + 1 else sbh l' := hinvh_l.2.1
    have hNode : sbh (Tree.Node l' (x', (c', h')) r') = h' := rfl
    by_cases hb : sbh (Tree.Node l' (x', (c', h')) r') ≤ sbh r
    · simp only [TsjoinR, ite_eq_left hb]
      omega
    · simp only [TsjoinR, ite_eq_right hb]
      cases c' with
      | Black =>
        simp only [eq_self_iff_true, ite_true] at hh'
        simp only [scol.eq_2, reduceCtorEq, ite_false]
        have hbh_r' : sbh r ≤ sbh r' := by omega
        have hIH := ihr r hinvc_r' hinvh_r' hbh_r'
        have hX : (if scol r' = .Red then (1:ℕ) else 0) ≤ 1 := by split <;> omega
        omega
      | Red =>
        simp only [reduceCtorEq, ite_false] at hh'
        simp only [scol.eq_2, eq_self_iff_true, ite_true]
        have hcol_r' : scol r' = .Black := (hinvc_l.1 rfl).2
        have hbh_r' : sbh r ≤ sbh r' := by omega
        have hIH := ihr r hinvc_r' hinvh_r' hbh_r'
        have hX : (if scol r' = .Red then (1:ℕ) else 0) = 0 := by simp [hcol_r']
        omega

/-- Cost rule, right-heavy case (AFP `rule_cost_R`). -/
public theorem srbt_rule_cost_R (l r : Tree α (Color × ℕ)) (x : α) (hl : srbt l) (hr : srbt r)
    (hbh : sbh r < sbh l) : Tsjoin l x r + srk r ≤ srk l + 2 := by
  have hT : Tsjoin l x r = TsjoinR l x r := by simp [Tsjoin, hbh]
  rw [hT]
  have hB := TsjoinR_bound l x r hl.1 hl.2 (le_of_lt hbh)
  cases hc : scol l with
  | Red =>
    have hsrk_l : srk l = 2 * sbh l + 1 := srk_of_scol_red l hc
    have hif : (if scol l = .Red then (1:ℕ) else 0) = 1 := by simp [hc]
    have hb2 := (srk_bounds r).2
    omega
  | Black =>
    have hsrk_l : srk l = 2 * sbh l := srk_of_scol_black l hc
    have hif : (if scol l = .Red then (1:ℕ) else 0) = 0 := by simp [hc]
    have hb2 := (srk_bounds r).2
    omega

/-- Cost rule, left-heavy case (AFP `rule_cost_L`). -/
public theorem srbt_rule_cost_L (l r : Tree α (Color × ℕ)) (x : α) (hl : srbt l) (hr : srbt r)
    (hbh : sbh l < sbh r) : Tsjoin l x r + srk l ≤ srk r + 2 := by
  have hT : Tsjoin l x r = TsjoinL l x r := by
    simp [Tsjoin, show ¬ sbh r < sbh l by omega, hbh]
  rw [hT]
  have hB := TsjoinL_bound l x r hr.1 hr.2 (le_of_lt hbh)
  cases hc : scol r with
  | Red =>
    have hsrk_r : srk r = 2 * sbh r + 1 := srk_of_scol_red r hc
    have hif : (if scol r = .Red then (1:ℕ) else 0) = 1 := by simp [hc]
    have hb2 := (srk_bounds l).2
    omega
  | Black =>
    have hsrk_r : srk r = 2 * sbh r := srk_of_scol_black r hc
    have hif : (if scol r = .Red then (1:ℕ) else 0) = 0 := by simp [hc]
    have hb2 := (srk_bounds l).2
    omega

/-- Cost rule, equal-height case (AFP `rule_cost_EQ`). -/
public theorem srbt_rule_cost_EQ (l r : Tree α (Color × ℕ)) (x : α) (h : sbh l = sbh r) :
    Tsjoin l x r = 0 := by
  simp [Tsjoin, show ¬ sbh r < sbh l by omega, show ¬ sbh l < sbh r by omega]

/-- The cost rule (AFP `rule_cost`): `Tsjoin` is bounded by `2 + |rk l - rk r|`. -/
public theorem srbt_rule_cost (l r : Tree α (Color × ℕ)) (x : α) (hl : srbt l) (hr : srbt r) :
    (Tsjoin l x r : ℝ) ≤ 2 + |(srk l : ℝ) - (srk r : ℝ)| := by
  rcases lt_trichotomy (sbh r) (sbh l) with h1 | h1 | h1
  · have hR : (Tsjoin l x r : ℝ) + (srk r : ℝ) ≤ (srk l : ℝ) + 2 := by
      exact_mod_cast srbt_rule_cost_R l r x hl hr h1
    have habs : (srk l : ℝ) - (srk r : ℝ) ≤ |(srk l : ℝ) - (srk r : ℝ)| :=
      le_abs_self _
    linarith
  · have hEQ : Tsjoin l x r = 0 := srbt_rule_cost_EQ l r x h1.symm
    rw [hEQ]
    push_cast
    have habs : (0:ℝ) ≤ |(srk l : ℝ) - (srk r : ℝ)| := abs_nonneg _
    linarith
  · have hL : (Tsjoin l x r : ℝ) + (srk l : ℝ) ≤ (srk r : ℝ) + 2 := by
      exact_mod_cast srbt_rule_cost_L l r x hl hr h1
    have habs : -((srk l : ℝ) - (srk r : ℝ)) ≤ |(srk l : ℝ) - (srk r : ℝ)| :=
      neg_le_abs _
    linarith

/-- The stored-height red–black `StronglyJoinableData` instance
(`StronglyJoinable`, `tree_rb`). -/
public def sStronglyJoinable : StronglyJoinableData α (Color × ℕ) where
  toJoinData := sjoinData
  rank := fun t => (srk t : ℝ)
  c_l := 1
  c_u := 2
  c_vals := ⟨by norm_num, by norm_num, by norm_num⟩
  rank_leaf := by simp [srk, sbh, scol]
  inv_balanced := fun t h => srbt_rule_bal t h
  T_join := Tsjoin
  k₀ := 2
  k₁ := 1
  rule_mono := by
    intro l r a hl hr
    exact_mod_cast (srk_sjoin l r a hl hr).1
  rule_sub := by
    intro l' l r' r a b x h1 h2 hl' hr' hnode
    exact srbt_rule_sub h1 h2 hl' hr' hnode
  join_size := by
    intro l r a hl hr
    exact tsize_sjoin l a r
  rule_cost := by
    intro l r a hl hr
    rw [one_mul]
    exact srbt_rule_cost l r a hl hr
  k₀_nonneg := by norm_num
  k₁_nonneg := by norm_num

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
