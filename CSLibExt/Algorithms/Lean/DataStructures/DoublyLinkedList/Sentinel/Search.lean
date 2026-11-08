/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Basic

import Mathlib.Data.List.Find

/-!
# Sentinel linked-list search

CLRS fourth edition, section 10.2, printed page 263. The query is stored in the
allocated sentinel key before following actual next pointers until a key matches.
The final identity test distinguishes a data match from the sentinel failure stop.
Canonical circular representation and CSLib TimeM are reused directly.

The selected-event model charges write1, initialization1, comparison1 per visit,
advance1 per mismatch and final identity1. Reads, proof terms and result construction
are free. Physical RAM, persistent storage copying and word/bit costs are not claimed.
-/

namespace Cslib.Algorithms.Lean.DoublyLinkedList

universe u v

@[no_expose] private def Step {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (key : Key) (next cursor : Fin capacity) : Prop :=
  ∃ node, store.get cursor = some node ∧ node.payload.1 ≠ key ∧ node.next = some next



@[no_expose] private def keyWrite {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (hs : (store.get s).isSome) :
    Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity :=
  let sentinel := (store.get s).get hs
  store.set s.val (some { sentinel with payload := (key, sentinel.payload.2) }) s.isLt

private lemma keyWrite_get {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (hs : (store.get s).isSome) (z : Fin capacity) :
    (keyWrite store s key hs).get z =
      if s = z then some { (store.get s).get hs with
        payload := (key, ((store.get s).get hs).payload.2) } else store.get z := by
  change (store.set s.val _ s.isLt)[z.val] =
    if s = z then some { (store.get s).get hs with
      payload := (key, ((store.get s).get hs).payload.2) } else store[z.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]



private lemma keyWrite_circular {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (hs : (store.get s).isSome)
    (ids : List (Fin capacity)) (rep : CircularRepresents store s ids) :
    CircularRepresents (keyWrite store s key hs) s ids := by
  obtain ⟨hnodup, hsnot, ⟨sentinel, hsentinel, hnext, hprev⟩, hnodes⟩ := rep
  have hget : (store.get s).get hs = sentinel :=
    Option.some.inj ((Option.some_get hs).trans hsentinel)
  refine ⟨hnodup, hsnot, ?_, ?_⟩
  · refine ⟨{ sentinel with payload := (key, sentinel.payload.2) }, ?_, hnext, hprev⟩
    rw [keyWrite_get]
    simp only [ite_true, hget]
  · intro before a after he
    obtain ⟨node, hn, hp, hnext⟩ := hnodes before a after he
    have ha : a ∈ ids := by
      rw [he]
      simp
    have hsa : s ≠ a := fun e => hsnot (e ▸ ha)
    refine ⟨node, ?_, hp, hnext⟩
    rw [keyWrite_get, ite_eq_right hsa]
    exact hn



private lemma circle_acc {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids)
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (after : List (Fin capacity)) :
    ∀ before, ids = before ++ after → Acc (Step store key) (after.headD s) := by
  induction after with
  | nil =>
    intro before he
    refine Acc.intro s ?_
    rintro next ⟨node, hn, hk, _⟩
    exact (hk (sentinelMatch node hn)).elim
  | cons a after ih =>
    intro before he
    obtain ⟨node, hn, _, hnext⟩ := rep.2.2.2 before a after he
    refine Acc.intro a ?_
    rintro next ⟨actual, ha, _, hanext⟩
    have hactual : actual = node := Option.some.inj (ha.symm.trans hn)
    subst actual
    have hcursor : next = after.headD s := Option.some.inj (hanext.symm.trans hnext)
    subst next
    apply ih (before ++ [a])
    simpa only [List.append_assoc, List.singleton_append] using he



private lemma circle_allocated {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) (cursor : Fin capacity)
    (hg : cursor = s ∨ cursor ∈ ids) : (store.get cursor).isSome := by
  rcases hg with rfl | hmem
  · obtain ⟨sentinel, hn, _, _⟩ := rep.2.2.1
    simp only [hn, Option.isSome_some]
  · obtain ⟨before, after, he⟩ := List.mem_iff_append.mp hmem
    obtain ⟨node, hn, _, _⟩ := rep.2.2.2 before cursor after he
    simp only [hn, Option.isSome_some]



@[no_expose] private def reachableLoop {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (key : Key) (Good : Fin capacity → Prop)
    (allocated : ∀ cursor, Good cursor → (store.get cursor).isSome)
    (nextGood : ∀ cursor (hg : Good cursor),
      ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key →
      ∃ hn : ((store.get cursor).get (allocated cursor hg)).next.isSome,
        Good (((store.get cursor).get (allocated cursor hg)).next.get hn))
    (cursor : Fin capacity) (acc : Acc (Step store key) cursor)
    (hg : Good cursor) : TimeM Nat (Fin capacity) :=
  acc.rec (motive := fun cursor _ => Good cursor → TimeM Nat (Fin capacity))
    (fun cursor _ recur hg => do
      let node := (store.get cursor).get (allocated cursor hg)
      TimeM.tick 1
      if hk : node.payload.1 = key then
        pure cursor
      else
        have hn : node.next.isSome := (nextGood cursor hg hk).choose
        let next := node.next.get hn
        TimeM.tick 1
        recur next ⟨node, (Option.some_get (allocated cursor hg)).symm, hk,
          (Option.some_get hn).symm⟩ (nextGood cursor hg hk).choose_spec) hg



private lemma circle_next_of_mem {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) (cursor : Fin capacity) (hmem : cursor ∈ ids)
    (hc : (store.get cursor).isSome) :
    ∃ hn : ((store.get cursor).get hc).next.isSome,
      ((store.get cursor).get hc).next.get hn = s ∨
        ((store.get cursor).get hc).next.get hn ∈ ids := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp hmem
  obtain ⟨node, hn, _, hnext⟩ := rep.2.2.2 before cursor after he
  have hget : (store.get cursor).get hc = node :=
    Option.some.inj ((Option.some_get hc).trans hn)
  have hsome : ((store.get cursor).get hc).next.isSome := by
    simp only [hget, hnext, Option.isSome_some]
  refine ⟨hsome, ?_⟩
  have heq : ((store.get cursor).get hc).next.get hsome = after.headD s :=
    Option.some.inj ((Option.some_get hsome).trans (by simpa only [hget] using hnext))
  rw [heq]
  cases after with
  | nil => exact Or.inl rfl
  | cons a after =>
    right
    rw [he]
    simp



private lemma keyWrite_match {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (hs : (store.get s).isSome)
    (node : Node (Key × Satellite) (Fin capacity))
    (hn : (keyWrite store s key hs).get s = some node) : node.payload.1 = key := by
  have hnode : { (store.get s).get hs with
      payload := (key, ((store.get s).get hs).payload.2) } = node :=
    Option.some.inj (by simpa only [keyWrite_get, ite_true] using hn)
  exact congrArg (fun n => n.payload.1) hnode.symm

private lemma circle_next_good {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids)
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (cursor : Fin capacity) (hg : cursor = s ∨ cursor ∈ ids)
    (hk : ((store.get cursor).get (circle_allocated store s ids rep cursor hg)).payload.1 ≠ key) :
    ∃ hn : ((store.get cursor).get (circle_allocated store s ids rep cursor hg)).next.isSome,
      ((store.get cursor).get (circle_allocated store s ids rep cursor hg)).next.get hn = s ∨
        ((store.get cursor).get (circle_allocated store s ids rep cursor hg)).next.get hn
          ∈ ids := by
  rcases hg with he | hmem
  · subst cursor
    exact (hk (sentinelMatch _ (Option.some_get _).symm)).elim
  · exact circle_next_of_mem store s ids rep cursor hmem _



private lemma circle_head_good {capacity : Nat} (s : Fin capacity) (ids : List (Fin capacity)) :
    ids.headD s = s ∨ ids.headD s ∈ ids := by
  cases ids with
  | nil => exact Or.inl rfl
  | cons a ids => exact Or.inr List.mem_cons_self

private lemma circle_sentinel_next {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) (hs : (store.get s).isSome) :
    ∃ hn : ((store.get s).get hs).next.isSome,
      ((store.get s).get hs).next.get hn = ids.headD s := by
  obtain ⟨sentinel, hn, hnext, _⟩ := rep.2.2.1
  have he : (store.get s).get hs = sentinel :=
    Option.some.inj ((Option.some_get hs).trans hn)
  have hsome : ((store.get s).get hs).next.isSome := by
    simp only [he, hnext, Option.isSome_some]
  exact ⟨hsome, Option.some.inj ((Option.some_get hsome).trans
    (by simpa only [he] using hnext))⟩



@[no_expose] private def OnCircle {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s cursor : Fin capacity) : Prop :=
  ∃ ids, CircularRepresents store s ids ∧ (cursor = s ∨ cursor ∈ ids)

private lemma onCircle_allocated {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s cursor : Fin capacity) (hg : OnCircle store s cursor) : (store.get cursor).isSome := by
  obtain ⟨ids, rep, hcursor⟩ := hg
  exact circle_allocated store s ids rep cursor hcursor

private lemma valid_sentinel {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (valid : ∃ ids, CircularRepresents store s ids) : OnCircle store s s := by
  obtain ⟨ids, rep⟩ := valid
  exact ⟨ids, rep, Or.inl rfl⟩



private lemma onCircle_acc {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key)
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (cursor : Fin capacity) (hg : OnCircle store s cursor) : Acc (Step store key) cursor := by
  obtain ⟨ids, rep, hcursor⟩ := hg
  rcases hcursor with he | hmem
  · subst cursor
    exact circle_acc store s key ids rep sentinelMatch [] ids (by simp)
  · obtain ⟨before, after, he⟩ := List.mem_iff_append.mp hmem
    exact circle_acc store s key ids rep sentinelMatch (cursor :: after) before he



private lemma onCircle_next {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key)
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (cursor : Fin capacity) (hg : OnCircle store s cursor)
    (hk : ((store.get cursor).get (onCircle_allocated store s cursor hg)).payload.1 ≠ key) :
    ∃ hn : ((store.get cursor).get (onCircle_allocated store s cursor hg)).next.isSome,
      OnCircle store s
        (((store.get cursor).get (onCircle_allocated store s cursor hg)).next.get hn) := by
  obtain ⟨ids, rep, hcursor⟩ := hg
  obtain ⟨hn, hnext⟩ := circle_next_good store s key ids rep sentinelMatch cursor hcursor hk
  exact ⟨hn, ids, rep, hnext⟩

private lemma valid_initial {Key : Type u} {Satellite : Type v} {capacity : Nat}
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (valid : ∃ ids, CircularRepresents store s ids)
    (hs : (store.get s).isSome) :
    ∃ hn : ((store.get s).get hs).next.isSome,
      OnCircle store s (((store.get s).get hs).next.get hn) := by
  obtain ⟨ids, rep⟩ := valid
  obtain ⟨hn, hnext⟩ := circle_sentinel_next store s ids rep hs
  exact ⟨hn, ids, rep, hnext.symm ▸ circle_head_good s ids⟩



/-- Runs CLRS sentinel search in source order, returning the modified pool and first
matching data identity. Only the sentinel key is overwritten; its old key is not restored.
The input circle witness is erased. Cost counts the write, initialization, comparisons,
mismatch advances and final identity test, not physical storage/bit operations. -/
public def listSearchSentinel {Key : Type u} {Satellite : Type v} {capacity : Nat} [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (valid : ∃ ids, CircularRepresents store s ids) :
    TimeM Nat (Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity ×
      Option (Fin capacity)) :=
  let hs := onCircle_allocated store s s (valid_sentinel store s valid)
  do
    TimeM.tick 1
    let updated := keyWrite store s key hs
    have updatedValid : ∃ ids, CircularRepresents updated s ids := by
      obtain ⟨ids, rep⟩ := valid
      exact ⟨ids, keyWrite_circular store s key hs ids rep⟩
    let allocated := onCircle_allocated updated s
    let sentinel := (updated.get s).get (allocated s (valid_sentinel updated s updatedValid))
    let nextProof := valid_initial updated s updatedValid
      (allocated s (valid_sentinel updated s updatedValid))
    TimeM.tick 1
    let cursor := sentinel.next.get nextProof.choose
    let hg := nextProof.choose_spec
    let acc := onCircle_acc updated s key (keyWrite_match store s key hs) cursor hg
    let scan := reachableLoop updated key (OnCircle updated s) allocated
      (onCircle_next updated s key (keyWrite_match store s key hs)) cursor acc hg
    TimeM.tick scan.time
    TimeM.tick 1
    pure (updated, if scan.ret = s then none else some scan.ret)



private lemma reachableLoop_hit {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (key : Key) (Good : Fin capacity → Prop)
    (allocated : ∀ cursor, Good cursor → (store.get cursor).isSome)
    (nextGood : ∀ cursor (hg : Good cursor),
      ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key →
      ∃ hn : ((store.get cursor).get (allocated cursor hg)).next.isSome,
        Good (((store.get cursor).get (allocated cursor hg)).next.get hn))
    (cursor : Fin capacity) (acc : Acc (Step store key) cursor) (hg : Good cursor)
    (hk : ((store.get cursor).get (allocated cursor hg)).payload.1 = key) :
    reachableLoop store key Good allocated nextGood cursor acc hg = ⟨cursor, 1⟩ := by
  cases acc
  apply TimeM.ext <;> simp [reachableLoop, hk]



private lemma reachableLoop_miss {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (key : Key) (Good : Fin capacity → Prop)
    (allocated : ∀ cursor, Good cursor → (store.get cursor).isSome)
    (nextGood : ∀ cursor (hg : Good cursor),
      ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key →
      ∃ hn : ((store.get cursor).get (allocated cursor hg)).next.isSome,
        Good (((store.get cursor).get (allocated cursor hg)).next.get hn))
    (cursor : Fin capacity) (acc : Acc (Step store key) cursor) (hg : Good cursor)
    (hk : ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key) :
    let node := (store.get cursor).get (allocated cursor hg)
    let hn := (nextGood cursor hg hk).choose
    let next := node.next.get hn
    let hstep : Step store key next cursor :=
      ⟨node, (Option.some_get (allocated cursor hg)).symm, hk, (Option.some_get hn).symm⟩
    let child := reachableLoop store key Good allocated nextGood next (acc.inv hstep)
      (nextGood cursor hg hk).choose_spec
    reachableLoop store key Good allocated nextGood cursor acc hg =
      ⟨child.ret, 2 + child.time⟩ := by
  cases acc
  apply TimeM.ext
  · simp only [reachableLoop, hk, ↓reduceDIte, TimeM.ret_bind]
  · simp only [reachableLoop, hk, ↓reduceDIte, TimeM.time_bind, TimeM.time_tick]
    rw [← Nat.add_assoc]

private lemma reachableLoop_empty {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (Good : Fin capacity → Prop)
    (allocated : ∀ cursor, Good cursor → (store.get cursor).isSome)
    (nextGood : ∀ cursor (hg : Good cursor),
      ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key →
      ∃ hn : ((store.get cursor).get (allocated cursor hg)).next.isSome,
        Good (((store.get cursor).get (allocated cursor hg)).next.get hn))
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (acc : Acc (Step store key) s) (hg : Good s) :
    reachableLoop store key Good allocated nextGood s acc hg = ⟨s, 1⟩ := by
  apply reachableLoop_hit
  exact sentinelMatch _ (Option.some_get (allocated s hg)).symm

private lemma reachableLoop_find {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (Good : Fin capacity → Prop)
    (allocated : ∀ cursor, Good cursor → (store.get cursor).isSome)
    (nextGood : ∀ cursor (hg : Good cursor),
      ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key →
      ∃ hn : ((store.get cursor).get (allocated cursor hg)).next.isSome,
        Good (((store.get cursor).get (allocated cursor hg)).next.get hn))
    (ids : List (Fin capacity)) (rep : CircularRepresents store s ids)
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (after : List (Fin capacity)) :
    ∀ before, ids = before ++ after →
      ∀ (acc : Acc (Step store key) (after.headD s)) (hg : Good (after.headD s)),
        (reachableLoop store key Good allocated nextGood (after.headD s) acc hg).ret =
          (after.find? (fun x => decide
            ((store.get x).map (fun node => node.payload.1) = some key))).getD s := by
  induction after with
  | nil =>
    intro before he acc hg
    have h := reachableLoop_empty store s key Good allocated nextGood sentinelMatch acc hg
    simpa using congrArg TimeM.ret h
  | cons a after ih =>
    intro before he acc hg
    obtain ⟨node, hn, _, hnext⟩ := rep.2.2.2 before a after he
    have actualEq : (store.get a).get (allocated a hg) = node := by simp [hn]
    by_cases hk : node.payload.1 = key
    · have h := reachableLoop_hit store key Good allocated nextGood a acc hg
        (by simpa only [actualEq] using hk)
      simpa [List.find?_cons, hn, hk] using congrArg TimeM.ret h
    · have h := reachableLoop_miss store key Good allocated nextGood a acc hg
        (by simpa only [actualEq] using hk)
      dsimp only at h
      simp only [actualEq, hnext, Option.get_some] at h
      have he' : ids = (before ++ [a]) ++ after := by
        simpa only [List.append_assoc, List.singleton_append] using he
      have child := ih (before ++ [a]) he'
      have retEq := congrArg TimeM.ret h
      simpa [List.find?_cons, hn, hk] using retEq.trans (child _ _)

private lemma reachableLoop_time {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (Good : Fin capacity → Prop)
    (allocated : ∀ cursor, Good cursor → (store.get cursor).isSome)
    (nextGood : ∀ cursor (hg : Good cursor),
      ((store.get cursor).get (allocated cursor hg)).payload.1 ≠ key →
      ∃ hn : ((store.get cursor).get (allocated cursor hg)).next.isSome,
        Good (((store.get cursor).get (allocated cursor hg)).next.get hn))
    (ids : List (Fin capacity)) (rep : CircularRepresents store s ids)
    (sentinelMatch : ∀ node, store.get s = some node → node.payload.1 = key)
    (after : List (Fin capacity)) :
    ∀ before, ids = before ++ after →
      ∀ (acc : Acc (Step store key) (after.headD s)) (hg : Good (after.headD s)),
        (reachableLoop store key Good allocated nextGood (after.headD s) acc hg).time =
          2 * (after.findIdx? (fun x => decide
            ((store.get x).map (fun node => node.payload.1) = some key))).getD
              after.length + 1 := by
  induction after with
  | nil =>
    intro before he acc hg
    have h := reachableLoop_empty store s key Good allocated nextGood sentinelMatch acc hg
    simpa using congrArg TimeM.time h
  | cons a after ih =>
    intro before he acc hg
    obtain ⟨node, hn, _, hnext⟩ := rep.2.2.2 before a after he
    have actualEq : (store.get a).get (allocated a hg) = node := by simp [hn]
    by_cases hk : node.payload.1 = key
    · have h := reachableLoop_hit store key Good allocated nextGood a acc hg
        (by simpa only [actualEq] using hk)
      simpa [List.findIdx?_cons, hn, hk] using congrArg TimeM.time h
    · have h := reachableLoop_miss store key Good allocated nextGood a acc hg
        (by simpa only [actualEq] using hk)
      dsimp only at h
      simp only [actualEq, hnext, Option.get_some] at h
      have he' : ids = (before ++ [a]) ++ after := by
        simpa only [List.append_assoc, List.singleton_append] using he
      have child := ih (before ++ [a]) he'
      have timeEq := congrArg TimeM.time h
      dsimp only at timeEq
      rw [child] at timeEq
      cases after.findIdx? (fun x => decide
          ((store.get x).map (fun node => node.payload.1) = some key)) <;>
        simp [List.findIdx?_cons, hn, hk] at timeEq ⊢ <;> omega

private lemma search_ret_store {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (valid : ∃ ids, CircularRepresents store s ids) :
    (listSearchSentinel store s key valid).ret.1 =
      keyWrite store s key (onCircle_allocated store s s (valid_sentinel store s valid)) := by
  rfl

private lemma keyWrite_find {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (hs : (store.get s).isSome)
    (ids : List (Fin capacity)) (hsnot : s ∉ ids) :
    ids.find? (fun x => decide
        (((keyWrite store s key hs).get x).map (fun node => node.payload.1) = some key)) =
      ids.find? (fun x => decide
        ((store.get x).map (fun node => node.payload.1) = some key)) := by
  apply List.find?_congr
  intro x hx
  have hsx : s ≠ x := fun he => hsnot (he ▸ hx)
  rw [keyWrite_get, ite_eq_right hsx]

private lemma keyWrite_findIdx {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (hs : (store.get s).isSome)
    (ids : List (Fin capacity)) (hsnot : s ∉ ids) :
    ids.findIdx? (fun x => decide
        (((keyWrite store s key hs).get x).map (fun node => node.payload.1) = some key)) =
      ids.findIdx? (fun x => decide
        ((store.get x).map (fun node => node.payload.1) = some key)) := by
  induction ids with
  | nil => rfl
  | cons x ids ih =>
    have hsx : s ≠ x := fun he => hsnot (he ▸ List.mem_cons_self)
    have htail : s ∉ ids := fun hx => hsnot (List.mem_cons_of_mem x hx)
    simp only [List.findIdx?_cons]
    rw [keyWrite_get, ite_eq_right hsx, ih htail]

private lemma mask_find {α : Type*} [DecidableEq α] (s : α) (ids : List α)
    (p : α → Bool) (hsnot : s ∉ ids) :
    (if (ids.find? p).getD s = s then none else some ((ids.find? p).getD s)) =
      ids.find? p := by
  cases he : ids.find? p with
  | none => simp
  | some a =>
    have ha : a ∈ ids := by
      obtain ⟨_, before, after, hsplit, _⟩ := List.find?_eq_some_iff_append.mp he
      rw [hsplit]
      simp
    have has : a ≠ s := fun he => hsnot (he ▸ ha)
    simp [has]

/-- The returned identity is the first pre-run data-node key match in circle order.
The sentinel is a stopping device, never a successful returned data identity. -/
public theorem listSearchSentinel_ret {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    (listSearchSentinel store s key ⟨ids, rep⟩).ret.2 =
      ids.find? (fun x => decide
        ((store.get x).map (fun node => node.payload.1) = some key)) := by
  let valid : ∃ ids, CircularRepresents store s ids := ⟨ids, rep⟩
  let hs := onCircle_allocated store s s (valid_sentinel store s valid)
  let updated := keyWrite store s key hs
  have rep' : CircularRepresents updated s ids := keyWrite_circular store s key hs ids rep
  let updatedValid : ∃ ids, CircularRepresents updated s ids := ⟨ids, rep'⟩
  let allocated := onCircle_allocated updated s
  let hs' := allocated s (valid_sentinel updated s updatedValid)
  let nextProof := valid_initial updated s updatedValid hs'
  let cursor := ((updated.get s).get hs').next.get nextProof.choose
  let hg := nextProof.choose_spec
  let nextGood := onCircle_next updated s key (keyWrite_match store s key hs)
  let acc := onCircle_acc updated s key (keyWrite_match store s key hs) cursor hg
  let scan := reachableLoop updated key (OnCircle updated s) allocated nextGood cursor acc hg
  have hcursor : cursor = ids.headD s := (circle_sentinel_next updated s ids rep' hs').choose_spec
  have hf : scan.ret = (ids.find? (fun x => decide
      ((updated.get x).map (fun node => node.payload.1) = some key))).getD s := by
    have H : ∀ (x : Fin capacity) (a : Acc (Step updated key) x) (h : OnCircle updated s x),
        x = ids.headD s →
          (reachableLoop updated key (OnCircle updated s) allocated nextGood x a h).ret =
            (ids.find? (fun z => decide
              ((updated.get z).map (fun node => node.payload.1) = some key))).getD s := by
      intro x a h he
      subst x
      exact reachableLoop_find updated s key (OnCircle updated s) allocated nextGood ids rep'
        (keyWrite_match store s key hs) ids [] (by simp) a h
    exact H cursor acc hg hcursor
  change (if scan.ret = s then none else some scan.ret) = _
  rw [hf, mask_find s ids _ rep'.2.1, keyWrite_find store s key hs ids rep.2.1]

/-- Exact selected-event cost: two events per preceding mismatching data node plus
four fixed events. An absent query scans the complete data circle. -/
public theorem listSearchSentinel_time {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    (listSearchSentinel store s key ⟨ids, rep⟩).time =
      2 * (ids.findIdx? (fun x => decide
        ((store.get x).map (fun node => node.payload.1) = some key))).getD ids.length + 4 := by
  let valid : ∃ ids, CircularRepresents store s ids := ⟨ids, rep⟩
  let hs := onCircle_allocated store s s (valid_sentinel store s valid)
  let updated := keyWrite store s key hs
  have rep' : CircularRepresents updated s ids := keyWrite_circular store s key hs ids rep
  let updatedValid : ∃ ids, CircularRepresents updated s ids := ⟨ids, rep'⟩
  let allocated := onCircle_allocated updated s
  let hs' := allocated s (valid_sentinel updated s updatedValid)
  let nextProof := valid_initial updated s updatedValid hs'
  let cursor := ((updated.get s).get hs').next.get nextProof.choose
  let hg := nextProof.choose_spec
  let nextGood := onCircle_next updated s key (keyWrite_match store s key hs)
  let acc := onCircle_acc updated s key (keyWrite_match store s key hs) cursor hg
  let scan := reachableLoop updated key (OnCircle updated s) allocated nextGood cursor acc hg
  have hcursor : cursor = ids.headD s := (circle_sentinel_next updated s ids rep' hs').choose_spec
  have ht : scan.time = 2 * (ids.findIdx? (fun x => decide
      ((updated.get x).map (fun node => node.payload.1) = some key))).getD ids.length + 1 := by
    have H : ∀ (x : Fin capacity) (a : Acc (Step updated key) x) (h : OnCircle updated s x),
        x = ids.headD s →
          (reachableLoop updated key (OnCircle updated s) allocated nextGood x a h).time =
            2 * (ids.findIdx? (fun z => decide
              ((updated.get z).map (fun node => node.payload.1) = some key))).getD
                ids.length + 1 := by
      intro x a h he
      subst x
      exact reachableLoop_time updated s key (OnCircle updated s) allocated nextGood ids rep'
        (keyWrite_match store s key hs) ids [] (by simp) a h
    exact H cursor acc hg hcursor
  change 1 + (1 + (scan.time + (1 + 0))) = _
  rw [ht, keyWrite_findIdx store s key hs ids rep.2.1]
  omega

/-- The complete returned pool differs only in the sentinel key; all other cells and
all next/prev links and satellite payloads are unchanged. -/
public theorem listSearchSentinel_get {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (valid : ∃ ids, CircularRepresents store s ids)
    (z : Fin capacity) :
    (listSearchSentinel store s key valid).ret.1.get z =
      if z = s then
        (store.get z).map (fun node => { node with payload := (key, node.payload.2) })
      else store.get z := by
  rw [search_ret_store, keyWrite_get]
  by_cases hz : z = s
  · subst z
    have hs := onCircle_allocated store s s (valid_sentinel store s valid)
    simp only [ite_true]
    conv_rhs => rw [← Option.some_get hs]
    rfl
  · have hsz : s ≠ z := fun he => hz he.symm
    rw [ite_eq_right hsz, ite_eq_right hz]

/-- Sentinel search preserves the same canonical represented circle. -/
public theorem listSearchSentinel_circular {Key : Type u} {Satellite : Type v} {capacity : Nat}
    [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    CircularRepresents (listSearchSentinel store s key ⟨ids, rep⟩).ret.1 s ids := by
  rw [search_ret_store]
  exact keyWrite_circular store s key _ ids rep

end Cslib.Algorithms.Lean.DoublyLinkedList
